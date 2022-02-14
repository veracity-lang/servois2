open Util
open Smt
open Spec
open Smt_parsing

exception SolverFailure of string

let () =
  Printexc.register_printer @@
  function
  | SolverFailure sl -> 
    Some (sp "Solver failure: \n%s\n" sl)
  | _ -> None


let n_queries = ref 0

type solve_result =
  | Sat of string
  | Unsat
  | Unknown

let bool_of_exp = function (* TODO *)
    | EConst(CBool t) -> t
    | _ -> failwith "bool_of_exp"

let parse_pred_data = compose (List.map (compose bool_of_exp snd)) values_of_string

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
    | _ -> raise @@ SolverFailure (String.concat "" out)

  let run (smt : string) : solve_result =
    let exec = find_exec "CVC4" exec_paths in
    let sout, serr = run_exec exec args smt in
    print_exec_result sout serr;
    n_queries := !n_queries + 1;
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
    | "sat" :: models -> Sat (String.concat "" models)
    | "unsat" :: _ -> Unsat
    | _ -> raise @@ SolverFailure (String.concat "\n" out)

  let run (smt : string) : solve_result =
    let exec = find_exec "CVC5" exec_paths in
    let sout, serr = run_exec exec args smt in
    print_exec_result sout serr;
    n_queries := !n_queries + 1;
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
    | "sat" :: models -> Sat (String.concat "" models)
    | "unsat" :: _ -> Unsat
    | _ -> raise @@ SolverFailure (String.concat "\n" out)

  let run (smt : string) : solve_result =
    let exec = find_exec "Z3" exec_paths in
    let sout, serr = run_exec exec args smt in
    print_exec_result sout serr;
    n_queries := !n_queries + 1;
    (* TODO handle any errors *)
    parse_output sout

end



module ProverMathSAT : Prover = struct
  let exec_paths =
    [ "/usr/local/bin/mathsat"
    ; "/usr/bin/mathsat"
    ]

  let args =
    [| ""; "-input=smt2" |]

  let parse_output (out : string list) =
    match out with
    | "sat" :: models -> Sat (String.concat "" models)
    | "unsat" :: _ -> Unsat
    | _ -> raise @@ SolverFailure (String.concat "\n" out)

  let run (smt : string) : solve_result =
    let exec = find_exec "Z3" exec_paths in
    let sout, serr = run_exec exec args smt in
    print_exec_result sout serr;
    n_queries := !n_queries + 1;
    (* TODO handle any errors *)
    parse_output sout

end
