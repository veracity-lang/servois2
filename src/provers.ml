open Util

exception SolverFailure of string list

type solve_result =
  | Valid
  | Invalid of string
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
    | ["sat"] -> Valid
    | ["unsat"] -> Invalid ""
    | _ -> raise @@ SolverFailure out

  let run (smt : string) : solve_result =
    let exec = find_exec "CVC4" exec_paths in
    let sout, serr = run_exec exec args smt in
    print_exec_result sout serr;
    (* TODO handle any errors *)
    parse_output sout

end