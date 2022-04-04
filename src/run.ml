open Util

module type Runner = sig
  val run : unit -> unit (* Uses all of argv *)
end

module CommonOptions = struct
  let debug = ref false
  let quiet = ref false
  let anons = ref []
  let output_file = ref ""
  let prover_name = ref ""
  let anon_fun (v : string) = anons := v :: !anons
  let common_speclist =
    [ "--debug", Arg.Set debug, " Display verbose debugging info during interpretation"
    ; "-d",      Arg.Set debug, " Short for --debug"
    ; "-o",      Arg.Set_string output_file, "<file> File to output to. Default file is stdout"
    ; "--prover", Arg.Set_string prover_name, "<name> Use a particular prover (default: CVC4)"
    ; "--quiet", Arg.Set quiet, " Print only the smt expression for the commutativity condition"
    ; "-q", Arg.Set quiet, " Short for --quiet"
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
    "Usage: " ^ exe_name ^ " synth [<flags>] <vcy program> m1;m2;m3:n1;n2;n3;etc"
  
  open CommonOptions
  
  let timeout = ref None

  let speclist =
    [ "--poke", Arg.Unit (fun () -> Choose.choose := Choose.poke), " Use servois poke heuristic (default: simple)"
    ; "--poke2", Arg.Unit (fun () -> Choose.choose := Choose.poke2), " Use improved poke heuristic (default: simple)"
    ; "--timeout", Arg.Float (fun f -> timeout := Some f), " Set time limit for execution"
    ] @ common_speclist |>
    Arg.align

  let synth yaml method_list =
    if !debug then begin
      Printexc.record_backtrace true;
      ignore @@ Parsing.set_trace true
    end;

    let spec =
      Yaml_util.yaml_of_file yaml |>
      Spec.spec_of_yaml
    in

    let prover : (module Provers.Prover) =
      match !prover_name |> String.lowercase_ascii with
      | "cvc4" -> (module Provers.ProverCVC4)
      | "cvc5" -> (module Provers.ProverCVC5)
      | "z3"   -> (module Provers.ProverZ3)
      | ""     -> (module Provers.ProverCVC4)
      | "mathsat" -> (module Provers.ProverMathSAT)
      | s      -> raise @@ Invalid_argument (sp "Unknown/unsupported prover '%s'" s)
    in
    
    let ms :: ns :: [] = String.split_on_char ':' method_list |> List.map (String.split_on_char ';') in

    let phi_comm, phi_noncomm =
      let synth_options = {
          Synth.default_synth_options with prover = get_prover ();
          timeout = !timeout
          } in
      Synth.synth ~options:synth_options spec ms ns 
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
    | [prog;method_list] -> synth prog method_list
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
    
    let verify yaml method_list cond =
        let open Solve in
        let open Spec in
        
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
        
        let ms_names :: ns_names :: [] = String.split_on_char ':' method_list |> List.map (String.split_on_char ';') in
       
        let valid = let verify_options = {
          Verify.default_verify_options with prover = get_prover ()
          } in Verify.verify ~options:verify_options spec ms_names ns_names cond_smt |> string_of_bool_option
        in
        
        let out_1 = if !quiet
            then valid ^ "\n"
            else sp "Valid: %s\n" valid
        in
        
        let out = if !complete
            then out_1 ^ begin
              let compl = let verify_options = {
                  Verify.default_verify_options with prover = get_prover (); ncom = true
                  } in Verify.verify ~options:verify_options spec ms_names ns_names (EUop(Not, cond_smt)) |> string_of_bool_option
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
      | [prog; method_list; cond] -> verify prog method_list cond
      | _ -> Arg.usage speclist (usage_msg Sys.argv.(0))
end

module RunTemp : Runner = struct

  let usage_msg exe_name =
    "Usage: " ^ exe_name ^ " temp [<flags>]\n    Synths commutativity conditions for OCaml representation of an object."
  
  open CommonOptions
  
  let timelimit = ref None
  
  let speclist =
    [ "--timeout", Arg.Float (fun f -> timelimit := Some f), " Set time limit for execution"
    ] @ common_speclist |>
    Arg.align

  let run () =
    Arg.current := 1;
    Arg.parse speclist anon_fun (usage_msg Sys.argv.(0));
    let anons = List.rev (!anons) in
    match anons with
    | [] -> 
        ()
    | _ -> Arg.usage speclist (usage_msg Sys.argv.(0))
end


type command =
  | CmdHelp (* Show help info *)
  | CmdSynth (* Synthesize phi *)
  | CmdVerify (* Verify validity of commutativity condition *)
  | CmdParse (* Parse YAML *)
  | CmdTemp

let command_map =
  [ "help",     CmdHelp
  ; "synth",    CmdSynth
  ; "verify",   CmdVerify
  ; "parse",    CmdParse
  ; "temp",     CmdTemp
  ]

let runner_map : (command * (module Runner)) list =
  [ CmdSynth,    (module RunSynth)
  ; CmdVerify,   (module RunVerify)
  ; CmdParse,  (module RunParse)
  ; CmdTemp,   (module RunTemp)
  ]

let display_help_message exe_name = 
  let details =
    "Commands:\n" ^
    "  help        Display this message\n" ^
    "  synth       Run inference\n" ^
    "  verify      Verify commutativity condition\n" ^
    "  parse       Parse yaml\n" ^
    "  temp        Do whatever the particular test implemented is\n"
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
