open Util
open Smt
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
  | Sat of (exp * exp) list
  | Unsat
  | Unknown

(* We instantiate the module with specific provers, e.g. CVC4, Z3 *)
module type Prover = sig
  val name : string
  val exec_paths : string list
  val args : string array
  val model_arg : string
  val parse_output : string list -> solve_result
end

let default_parse_output = function
    | "sat" :: models -> Sat (values_of_string @@ String.concat "" models) (* TODO: Maybe this should be a list of strings (parsed to a list of expressions?) *)
    | "unsat" :: _ -> Unsat
    | "unknown" :: _ -> Unknown
    | out -> raise @@ SolverFailure (String.concat "" out)

let run_prover ?(model=true) (prover : (module Prover)) (smt : string) : string list =
    let module P = (val prover) in
    let exec = find_exec P.name P.exec_paths in
    let args = if model then (Array.append P.args [| P.model_arg |]) else P.args in
    let sout, serr = run_exec exec args smt in
    print_exec_result sout serr;
    n_queries := !n_queries + 1;
    sout

let parse_prover_output (prover : (module Prover)) out : solve_result =
    let module P = (val prover) in
    P.parse_output out

module ProverCVC4 : Prover = struct
  let name = "CVC4"

  let exec_paths =
    [ "/usr/local/bin/cvc4"
    ; "/usr/bin/cvc4"
    ]

  let args =
    [| ""; "--lang"; "smt2"; "--incremental" |]
    
  let model_arg = "--produce-models"

  let parse_output = default_parse_output

end



module ProverCVC5 : Prover = struct
  let name = "CVC5"

  let exec_paths =
    [ "/usr/local/bin/cvc5"
    ; "/usr/bin/cvc5"
    ]

  let args =
    [| ""; "--lang"; "smt2"; "--incremental" |]
    
  let model_arg = "--produce-models"

  let parse_output = default_parse_output

end


module ProverZ3 : Prover = struct
  let name = "Z3"

  let exec_paths =
    [ "/usr/local/bin/z3"
    ; "/usr/bin/z3"
    ]

  let args =
    [| ""; "-smt2"; "-in" |]
    
  let model_arg = ""

  let parse_output = default_parse_output

end



module ProverMathSAT : Prover = struct
  let name = "Z3" (* TODO: Is this correct? *)

  let exec_paths =
    [ "/usr/local/bin/mathsat"
    ; "/usr/bin/mathsat"
    ]

  let args =
    [| ""; "-input=smt2" |]
    
  let model_arg = "-model"

  let parse_output = function
    | "sat" :: models -> let inp = (String.concat "" models) in let lexbuf = lex inp in
        Fun.const () @@ parse_partial (lexbuf, inp) Smt_parser.values_top;
        Sat (parse_partial (lexbuf, inp) Smt_parser.values_top) |>
        seq @@ parse_partial (lexbuf, inp) Smt_parser.eof_top
    | "unsat" :: _ -> Unsat
    | "unknown" :: _ -> Unknown
    | out -> raise @@ SolverFailure (String.concat "" out)

end
