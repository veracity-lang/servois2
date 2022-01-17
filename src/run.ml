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


module RunPhi : Runner = struct
  let usage_msg exe_name =
    "Usage: " ^ exe_name ^ " phi [<flags>] <vcy program> <method 1> <method 2>"
  
  let debug = ref false

  let anons = ref []

  let anon_fun (v : string) =
    anons := v :: !anons

  let output_file = ref ""
  let input_yaml = ref ""

  let speclist =
    [ "-d",      Arg.Set debug, " Display verbose debugging info during interpretation"
    ; "--debug", Arg.Set debug, " Display verbose debugging info during interpretation"
    ; "-o",      Arg.Set_string output_file, "<file> Output generated condition to file. Default file is stdout."
    ; "-y",      Arg.Set_string input_yaml, "<file> Use an existing YAML file. Uses vcy YAML generator by default"
    ] |>
    Arg.align

  let generate_phi prog_name method1 method2 =
    (* if !debug then begin
      Printexc.record_backtrace true
    end;

    let prog = Driver.parse_oat_file prog_name in
    let env = Interp.initialize_env prog false in

    let yaml =
      if !input_yaml = ""
      then Yaml_generator.compile_file_to_yaml prog_name prog
      else
        let in_chan = open_in !input_yaml in
        String.concat "\n" @@ read_all_in in_chan
    in

    let res =
      try
        Analyze.invoke_servois yaml method1 method2 |>
        Analyze.exp_of_servois_output env |>
        Ast.no_loc |>
        Astlib.AstPP.string_of_exp
      with e ->
        raise @@ Failure "Phi generation failed"
    in

    if !output_file = ""
    then Printf.printf "%s\n" res
    else
      let out_chan = open_out !output_file in
      output_string out_chan res;
      close_out out_chan *)
      failwith "revise later!"

  (* Assumes argc > 2 and argv[1] = "interface" *)
  let run () =
    Arg.current := 1;
    Arg.parse speclist anon_fun (usage_msg Sys.argv.(0));
    let anons = List.rev (!anons) in
    match anons with
    | [prog;method1;method2] -> generate_phi prog method1 method2
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
  | CmdPhi (* Synthesize phi *)
  | CmdParse (* Parse YAML *)
  | CmdTemp

let command_map =
  [ "help",     CmdHelp
  ; "synth",    CmdPhi
  ; "parse",    CmdParse
  ; "temp",     CmdTemp
  ]

let runner_map : (command * (module Runner)) list =
  [ CmdPhi,    (module RunPhi)
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
