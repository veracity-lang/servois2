(* TODO: command line stuff *)

open Util

module type Runner = sig
  val run : unit -> unit (* Uses all of argv *)
end


module RunParse : Runner = struct
  let usage_msg exe_name =
    "Usage: " ^ exe_name ^ " parse [<flags>] <YAML file>"
  
  let debug = ref false

  let anons = ref []

  let anon_fun (v : string) =
    anons := v :: !anons

  let output_file = ref ""

  let speclist =
    [ "-d",      Arg.Set debug, " Display verbose debugging info during interpretation"
    ; "--debug", Arg.Set debug, " Display verbose debugging info during interpretation"
    ; "-o",      Arg.Set_string output_file, "<file> Output parsing to file (defaults to stdout)"
    ] |>
    Arg.align

  let parse yaml =
    if !debug then begin
      Printexc.record_backtrace true;
      ignore @@ Parsing.set_trace true
    end;

    let parsed =
      Yaml_util.yaml_of_file yaml |>
      Yaml_util.string_of_value
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

  let anons = ref []

  let anon_fun (v : string) =
    anons := v :: !anons

  let output_file = ref ""

  let speclist =
    [ "-d",      Arg.Set debug, " Display verbose debugging info during interpretation"
    ; "--debug", Arg.Set debug, " Display verbose debugging info during interpretation"
    ; "-o",      Arg.Set_string output_file, "<file> Output generated condition to file. Default file is stdout."
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

    let phi_comm, phi_noncomm =
      Synth.synth spec method1 method2 
    in

    let s_phi_comm    = Phi.ToString.t phi_comm in
    let s_phi_noncomm = Phi.ToString.t phi_noncomm in

    let out =
      sp "phi = %s\nphi-tilde = %s\n" 
      s_phi_comm s_phi_noncomm
    in

    if !output_file = ""
    then print_string out
    else
      let out_chan = open_out !output_file in
      output_string out_chan out;
      close_out out_chan

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
  let run () =
    let spec = Counter_example.spec in
    let phi, phi_tilde = Synth.synth spec "increment" "decrement" in
    print_string (Phi.string_of_disj phi); print_newline ();
    print_string (Phi.string_of_disj phi_tilde); print_newline()
    
    (*
    let m1 = Spec.get_method spec "increment" in
    let m2 = Spec.get_method spec "decrement" in
    let open Smt in
    let smt_exp = Synth.commute (Phi.smt_of_disj @@ Phi.Disj [Conj [EBop (Gt, EVar (Var "contents"), EConst (CInt 0))]]) in
    let query = Solve.string_of_smt_query spec m1 m2 smt_exp in

    let temp_out = open_out "../stuff/query.smt" in
    output_string temp_out query;
    close_out temp_out;

    let r = Provers.ProverCVC4.run query in

    match r with
    | Provers.Sat -> print_string "Valid\n"
    | Provers.Unsat m -> Printf.printf "Invalid: %s\n" m
    | Provers.Unknown -> print_string "Unknown\n"
    *)
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
