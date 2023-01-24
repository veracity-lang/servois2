open Servois2
open Util

module type Runner = sig
  val run : unit -> unit (* Uses all of argv *)
end

module CommonOptions = struct
  let debug = ref false
  let anons = ref []
  let output_file = ref ""
  let prover_name = ref ""
  let anon_fun (v : string) = anons := v :: !anons
  let common_speclist =
    [ "--debug", Arg.Set debug, " Display verbose debugging info during interpretation"
    ; "-d",      Arg.Set debug, " Short for --debug"
    ; "-o",      Arg.Set_string output_file, "<file> File to output to. Default file is stdout"
    ; "--prover", Arg.Set_string prover_name, "<name> Use a particular prover (default: CVC4)"
    ; "--quiet", Arg.Set Util.quiet, " Print only the smt expression for the commutativity condition"
    ; "-q", Arg.Set Util.quiet, " Short for --quiet"
    ; "--verbose", Arg.Set Util.verbosity, " Verbose output"
    ; "-v", Arg.Set Util.verbosity, " Short for --verbose"
    ; "--very-verbose", Arg.Set Util.very_verbose, " Very verbose output and print smt query files"
    ; "-vv", Arg.Set Util.very_verbose, " Short for --very-verbose"
    ; "--leftmover", Arg.Unit (fun () -> Solve.mode := Solve.LeftMover), " Synthesize left-mover condition (default: bowtie)"
    ; "--rightmover", Arg.Unit (fun () -> Solve.mode := Solve.RightMover), " Synthesize right-mover condition (default: bowtie)"
    ]
    
  let get_prover () : (module Provers.Prover) =
      match !prover_name |> String.lowercase_ascii with
      | "cvc4" -> (module Provers.ProverCVC4)
      | "cvc5" -> (module Provers.ProverCVC5)
      | "z3"   -> (module Provers.ProverZ3)
      | ""     -> (module Provers.ProverCVC4)
      | "mathsat" -> (module Provers.ProverMathSAT)
      | s      -> raise @@ Invalid_argument (sp "Unknown/unsupported prover '%s'" s)

end

module RunParse : Runner = struct
  let usage_msg exe_name =
    "Usage: " ^ exe_name ^ " parse [<flags>] <YAML file>"
  
  open CommonOptions
  
  let just_yaml = ref false

  let speclist =
    [ "-d",      Arg.Set debug, " Display verbose debugging info during interpretation"
    ; "--debug", Arg.Set debug, " Display verbose debugging info during interpretation"
    ; "-y",      Arg.Set just_yaml, " Just parse YAML; don't convert to a spec"
    ; "-o",      Arg.Set_string output_file, "<file> Output parsing to file (defaults to stdout)"
    ] |>
    Arg.align

  let parse yaml =
    if !debug then begin
      Printexc.record_backtrace true;
      ignore @@ Parsing.set_trace true
    end;

    let parsed =
      if !just_yaml
      then
        Yaml_util.yaml_of_file yaml |>
        Yaml_util.string_of_value
      else
        Yaml_util.yaml_of_file yaml |>
        Spec.spec_of_yaml |>
        Spec.Spec_ToMLString.spec
    in

    if !output_file = ""
    then Printf.printf "%s\n" parsed
    else
      let out_chan = open_out !output_file in
      output_string out_chan parsed;
      close_out out_chan

  (* Assumes argc > 2 and argv[1] = "parse" *)
  let run () =
    Arg.current := 1;
    Arg.parse speclist anon_fun (usage_msg Sys.argv.(0));
    let anons = List.rev (!anons) in
    match anons with
    | [prog] -> parse prog
    | _ -> Arg.usage speclist (usage_msg Sys.argv.(0))

end


module RunSynth : Runner = struct
  let usage_msg exe_name =
    "Usage: " ^ exe_name ^ " synth [<flags>] <vcy program> <method 1> <method 2>"
  
  open CommonOptions
  
  let timeout = ref None
  let lattice = ref false
  let stronger_pred_first = ref false
  let no_cache = ref true

  let speclist =
    [ "--poke", Arg.Unit (fun () -> Choose.choose := Choose.poke), " Use servois poke heuristic (default: simple)"
    ; "--poke2", Arg.Unit (fun () -> Choose.choose := Choose.poke2), " Use improved poke heuristic (default: simple)"
    ; "--mcpeak-bisect", Arg.Unit (fun () -> Choose.choose := Choose.mc_bisect), " Use model counting based synthesis with strategy: bisection"    
    ; "--mcpeak-max", Arg.Unit (fun () -> Choose.choose := Choose.mc_max), " Use model counting based synthesis with strategy: maximum-coverage"
    ; "--stronger-pred-first", Arg.Unit (fun () -> stronger_pred_first := true), " Choose stronger predicates first"
    ; "--lattice", Arg.Unit (fun () -> lattice := true), " Create and use lattice of predicate implication"
    ; "--timeout", Arg.Float (fun f -> timeout := Some f), " Set time limit for execution"
    ; "--auto-terms", Arg.Unit (fun () -> Predicate.autogen_terms := true), " Automatically generate terms from method specifications"
    ; "--cache", Arg.Unit (fun () -> no_cache := false), " Use cached implication lattice"
    ] @ common_speclist |>
    Arg.align

  let synth yaml method1 method2 =
    if !debug then begin
      Printexc.record_backtrace true;
      ignore @@ Parsing.set_trace true
    end;

    let spec =
      Yaml_util.yaml_of_file yaml |>
      Spec.spec_of_yaml
    in

    let phi_comm, phi_noncomm =
      let synth_options = {
        Synth.default_synth_options with prover = get_prover ();
                                         timeout = !timeout;
                                         lattice = !lattice;
                                         no_cache = !no_cache;
                                         stronger_predicates_first = !stronger_pred_first;
      } in
      Synth.synth ~options:synth_options spec method1 method2
    in

    let s_phi_comm    = Phi.ToString.t phi_comm in
    let s_phi_noncomm = Phi.ToString.t phi_noncomm in

    let out =
      if !quiet then s_phi_comm ^ "\n" else
      sp "phi = %s\nphi-tilde = %s\n" 
      s_phi_comm s_phi_noncomm
    in

    begin if !output_file = ""
    then print_string out
    else
      let out_chan = open_out !output_file in
      output_string out_chan out;
      close_out out_chan
    end;
    epf "%s\n" (Synth.string_of_benches !Synth.last_benchmarks)

      
  (* Assumes argc > 2 and argv[1] = "synth" *)
  let run () =
    Arg.current := 1;
    Arg.parse speclist anon_fun (usage_msg Sys.argv.(0));
    let anons = List.rev (!anons) in
    match anons with
    | [prog;method1;method2] -> synth prog method1 method2
    | _ -> Arg.usage speclist (usage_msg Sys.argv.(0))
end

module RunVerify : Runner = struct
    let usage_msg = sp "Usage: %s verify <yaml file> <method 1> <method 2> <condition> [flags]"
    
    open CommonOptions
    
    let ncom = ref false
    let complete = ref false
    
    let speclist = 
      [ "--ncom", Arg.Set ncom, " Verify non-commutativity condition instead of commutativity condition."
      ; "--complete", Arg.Set complete, " Also verify completeness."
      ] @ common_speclist |> Arg.align
    
    let run_verify yaml m1 m2 cond =
        
        let spec =
          Yaml_util.yaml_of_file yaml |>
          Spec.spec_of_yaml
        in
        
        let cond_smt = Smt_parsing.exp_of_string cond in
        
        let string_of_bool_option = function
            | Some true -> "true"
            | Some false -> "false"
            | _ -> "unknown"
        in
        
        let valid = let verify_options = {
          Verify.default_verify_options with prover = get_prover ()
          } in Verify.verify ~options:verify_options spec m1 m2 cond_smt |> string_of_bool_option
        in
        
        let out_1 = if !quiet
            then valid ^ "\n"
            else sp "Valid: %s\n" valid
        in
        
        let out = if !complete
            then out_1 ^ begin
              let compl = let verify_options = {
                  Verify.default_verify_options with prover = get_prover (); ncom = true
                  } in Verify.verify ~options:verify_options spec m1 m2 (EUop(Not, cond_smt)) |> string_of_bool_option
              in if !quiet then compl ^ "\n" else sp "Complete: %s\n" compl
            end
            else out_1
        in
        
        begin if !output_file = ""
        then print_string out
        else
          let out_chan = open_out !output_file in
          output_string out_chan out;
          close_out out_chan
        end
    
    let run () =
      Arg.current := 1;
      Arg.parse speclist anon_fun (usage_msg Sys.argv.(0));
      let anons = List.rev (!anons) in
      match anons with
      | [prog; m1; m2; cond] -> run_verify prog m1 m2 cond
      | _ -> Arg.usage speclist (usage_msg Sys.argv.(0))
end

module RunLattice : Runner = struct
    let usage_msg = sp "Usage: %s lattice <yaml file> [flags]"
    
    open CommonOptions
    
    let speclist = 
      [ "--auto-terms", Arg.Unit (fun () -> Predicate.autogen_terms := true), " Automatically generate terms from method specifications"] @
      common_speclist |> Arg.align
    
    let run_lattice yaml =
        
        let spec =
          Yaml_util.yaml_of_file yaml |>
          Spec.spec_of_yaml
        in
        
        let prover = get_prover () in
        
        let start_time = Unix.gettimeofday () in
        
        let all_ms_mangled = List.concat_map (fun m -> [Spec.mangle_method_vars true m; Spec.mangle_method_vars false m]) spec.methods in
        
        let preds_unfiltered = Predicate.generate_predicates spec all_ms_mangled in
        let preds = Solve.filter_predicates prover spec preds_unfiltered in
        
        let ps, pps, pequivc = Predicate_analyzer.observe_rels prover spec preds in
        let l = Choose.L.construct ps in
        
        let lattice_construct_time = Unix.gettimeofday () -. start_time in
        
        let lattice_fname = sp "%s.lattice" @@ if !output_file = "" then spec.name else !output_file in
        let equivc_fname = sp "%s.equivc_fname" @@ if !output_file = "" then spec.name else !output_file in
        
        let outc = open_out lattice_fname in
        Choose.L.save l outc; close_out outc;
        let outc = open_out equivc_fname in
        Predicate_analyzer.save_equivc outc pequivc;
        close_out outc;
        
        epf "time_lattice_construct, %.6f" (lattice_construct_time)
    
    let run () =
      Arg.current := 1;
      Arg.parse speclist anon_fun (usage_msg Sys.argv.(0));
      let anons = List.rev (!anons) in
      match anons with
      | [prog] -> run_lattice prog
      | _ -> Arg.usage speclist (usage_msg Sys.argv.(0))
end

type command =
  | CmdHelp (* Show help info *)
  | CmdSynth (* Synthesize phi *)
  | CmdVerify (* Verify validity of commutativity condition *)
  | CmdParse (* Parse YAML *)
  | CmdLattice

let command_map =
  [ "help",     CmdHelp
  ; "synth",    CmdSynth
  ; "verify",   CmdVerify
  ; "parse",    CmdParse
  ; "lattice",  CmdLattice
  ]

let runner_map : (command * (module Runner)) list =
  [ CmdSynth,    (module RunSynth)
  ; CmdVerify,   (module RunVerify)
  ; CmdParse,    (module RunParse)
  ; CmdLattice,  (module RunLattice)
  ]

let display_help_message exe_name = 
  let details =
    "Commands:\n" ^
    "  help        Display this message\n" ^
    "  synth       Run inference\n" ^
    "  verify      Verify commutativity condition\n" ^
    "  parse       Parse yaml\n"
  in Printf.eprintf "Usage: %s <command> [<flags>] [<args>]\n%s" exe_name details

(* Check first argument for command *)
let run () =
  match Sys.argv with
  | [| |] -> raise @@ UnreachableFailure "Empty argv"
  | [| exe_name |] -> display_help_message exe_name
  | _ ->
    (*Sys.chdir @@ Filename.dirname Sys.argv.(0); (* Make working directory relative to executable *)*)
    let exe_name, cmd = Sys.argv.(0), Sys.argv.(1) in
    match List.assoc_opt Sys.argv.(1) command_map with
    | None -> (* Unknown command *)
      Printf.eprintf "Unknown command \"%s\".\n" cmd;
      display_help_message exe_name
    | Some CmdHelp ->
      display_help_message exe_name
    | Some cmd ->
      let module R =
        (val (List.assoc cmd runner_map))
      in R.run ()

let () = run ()
