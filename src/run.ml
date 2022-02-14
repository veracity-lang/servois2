(* TODO: command line stuff *)

open Util

module type Runner = sig
  val run : unit -> unit (* Uses all of argv *)
end


module RunParse : Runner = struct
  let usage_msg exe_name =
    "Usage: " ^ exe_name ^ " parse [<flags>] <YAML file>"
  
  let debug = ref false

  let just_yaml = ref false

  let anons = ref []

  let anon_fun (v : string) =
    anons := v :: !anons

  let output_file = ref ""

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
  
  let debug = ref false
  let timeout = ref None

  let anons = ref []

  let anon_fun (v : string) =
    anons := v :: !anons

  let output_file = ref ""

  let prover_name = ref ""

  let speclist =
    [ "--poke", Arg.Unit (fun () -> Choose.choose := Choose.poke), " Use servois poke heuristic (default: simple)"
    ; "--poke2", Arg.Unit (fun () -> Choose.choose := Choose.poke2), " Use improved poke heuristic (default: simple)"
    ; "--timeout", Arg.Float (fun f -> timeout := Some f), " Set time limit for execution"
    ; "-o",      Arg.Set_string output_file, "<file> Output generated condition to file. Default file is stdout"
    ; "--prover", Arg.Set_string prover_name, "<name> Use a particular prover (default: CVC4)"
    ; "-d",      Arg.Set debug, " Display verbose debugging info during interpretation"
    ; "--debug", Arg.Set debug, " Display verbose debugging info during interpretation"
    ; "--verbose", Arg.Set Util.verbosity, " Verbose intermediate and error output"
    ; "--leftmover", Arg.Unit (fun () -> Solve.mode := Solve.LeftMover), " Synthesize left-mover condition (default: bowtie)"
    ; "--rightmover", Arg.Unit (fun () -> Solve.mode := Solve.RightMover), " Synthesize right-mover condition (default: bowtie)"
    ] |>
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

    let prover : (module Provers.Prover) =
      match !prover_name |> String.lowercase_ascii with
      | "cvc4" -> (module Provers.ProverCVC4)
      | "cvc5" -> (module Provers.ProverCVC5)
      | "z3"   -> (module Provers.ProverZ3)
      | ""     -> (module Provers.ProverCVC4)
      | s      -> raise @@ Invalid_argument (sp "Unknown/unsupported prover '%s'" s)
    in

    let phi_comm, phi_noncomm =
      let synth_options = {
          Synth.default_synth_options with prover = prover;
          timeout = !timeout
          } in
      Synth.synth ~options:synth_options spec method1 method2 
    in

    let s_phi_comm    = Phi.ToString.t phi_comm in
    let s_phi_noncomm = Phi.ToString.t phi_noncomm in

    let out =
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

module RunTemp : Runner = struct

  let usage_msg exe_name =
    "Usage: " ^ exe_name ^ " temp [<flags>]\n    Synths commutativity conditions for OCaml representation of an object."
  
  let debug = ref false
  let poke = ref false
  let timelimit = ref None
  
  let anons = ref []
  let anon_fun (v : string) =
    anons := v :: !anons

  let speclist =
    [ "-d",      Arg.Set debug, " Display verbose debugging info during interpretation"
    ; "--debug", Arg.Set debug, " Display verbose debugging info during interpretation"
    ; "--poke", Arg.Set poke, " Use the poke heuristic"
    ; "--verbose", Arg.Set (Util.verbosity), " Verbose!" 
    ; "--timeout", Arg.Float (fun f -> timelimit := Some f), " Set time limit for execution"
    ] |>
    Arg.align

  let run () =
    Arg.current := 1;
    Arg.parse speclist anon_fun (usage_msg Sys.argv.(0));
    let anons = List.rev (!anons) in
    match anons with
    | [] -> 
        if !debug then begin
            Printexc.record_backtrace true;
            ignore @@ Parsing.set_trace true end
            else ();
        if !poke then Choose.choose := Choose.poke else ();
        let spec = Counter_example.spec in
        let options = { Synth.default_synth_options with timeout = !timelimit } in
        let phi, phi_tilde = Synth.synth ~options:options spec "increment" "decrement" in
        print_string (Phi.string_of_disj phi); print_newline ();
        print_string (Phi.string_of_disj phi_tilde); print_newline();
        epf "Last benches:\n%s\n" @@ Synth.string_of_benches !Synth.last_benchmarks
    | _ -> Arg.usage speclist (usage_msg Sys.argv.(0))
end


type command =
  | CmdHelp (* Show help info *)
  | CmdSynth (* Synthesize phi *)
  | CmdParse (* Parse YAML *)
  | CmdTemp

let command_map =
  [ "help",     CmdHelp
  ; "synth",    CmdSynth
  ; "parse",    CmdParse
  ; "temp",     CmdTemp
  ]

let runner_map : (command * (module Runner)) list =
  [ CmdSynth,    (module RunSynth)
  ; CmdParse,  (module RunParse)
  ; CmdTemp,   (module RunTemp)
  ]

let display_help_message exe_name = 
  let details =
    "Commands:\n" ^
    "  help        Display this message\n" ^
    "  synth       Run inference\n" ^
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
