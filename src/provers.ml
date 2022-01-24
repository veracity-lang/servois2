open Util

exception SolverFailure of string list

type solve_result =
  | Sat of string
  | Unsat
  | Unknown




(* We instantiate the module with specific provers, e.g. CVC4, Z3 *)
module type Prover = sig
  val run : string -> solve_result
end


module ProverCVC4 : Prover = struct
  let exec_paths =
    [ "/usr/local/bin/cvc4"
    ; "/usr/bin/cvc4"
    ]

  let args =
    [| ""; "--lang"; "smt2"; "--produce-models" |]

  let parse_output (out : string list) =
    match out with
    | "sat" :: models -> Sat (String.concat "" models) (* TODO: Maybe this should be a list of strings (parsed to a list of expressions?) *) (* TODO: Do the same for the other provers *)
    | "unsat" :: _ -> Unsat
    | _ -> raise @@ SolverFailure out

  let run (smt : string) : solve_result =
    let exec = find_exec "CVC4" exec_paths in
    let sout, serr = run_exec exec args smt in
    print_exec_result sout serr;
    (* TODO handle any errors *)
    parse_output sout

end


module ProverZ3 : Prover = struct
  let exec_paths =
    [ "/usr/local/bin/z3"
    ; "/usr/bin/z3"
    ]

  let args =
    [| ""; "-smt2"; "-in" |]

  let parse_output (out : string list) =
    match out with
    | ["sat"] -> Sat ""
    | ["unsat"] -> Unsat
    | _ -> raise @@ SolverFailure out

  let run (smt : string) : solve_result =
    let exec = find_exec "Z3" exec_paths in
    let sout, serr = run_exec exec args smt in
    print_exec_result sout serr;
    (* TODO handle any errors *)
    parse_output sout

end



module ProverCVC5 : Prover = struct
  let exec_paths =
    [ "/usr/local/bin/cvc5"
    ; "/usr/bin/cvc5"
    ]

  let args =
    [| ""; "--lang"; "smt2"; "--produce-models" |]

  let parse_output (out : string list) =
    match out with
    | ["sat"] -> Sat ""
    | ["unsat"] -> Unsat
    | _ -> raise @@ SolverFailure out

  let run (smt : string) : solve_result =
    let exec = find_exec "CVC5" exec_paths in
    let sout, serr = run_exec exec args smt in
    print_exec_result sout serr;
    (* TODO handle any errors *)
    parse_output sout

end
