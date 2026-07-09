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
  val parse_output : string list -> solve_result
end

let default_parse_output = function
    | "sat" :: models -> if null models then Sat [] else Sat (values_of_string @@ String.concat "" models) (* TODO: Maybe this should be a list of strings (parsed to a list of expressions?) *)
    | "unsat" :: _ -> Unsat
    | "unknown" :: _ -> Unknown
    | out -> raise @@ SolverFailure (String.concat "" out)

let run_prover (prover : (module Prover)) (smt : string) : string list =
    let module P = (val prover) in
    let exec = find_exec P.name P.exec_paths in
    let sout, serr = run_exec exec P.args smt in
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
    [| ""; "--lang"; "smt2"; "--produce-models"; "--incremental"; "--fmf-fun"; "--strings-exp" |]

  let parse_output = default_parse_output

end



module ProverCVC5 : Prover = struct
  let name = "CVC5"

  let exec_paths =
    [ "/usr/local/bin/cvc5"
    ; "/usr/bin/cvc5"
    ]

  let args =
    (* --full-saturate-quant: enumerative/full-saturation instantiation. The -ae
       bowtie encodes havoc'd arrays as existentially-quantified array vars; the
       default instantiation strategy returns "unknown" on the resulting
       store-vs-havoc goals (e.g. proving an array WRITE right-commutes past a
       whole-array havoc). Full-saturation instantiation discharges them.
       --tlimit-per=12000: per-check-sat wall-clock limit (120s). CVC5 returns
       "unknown" (→ Unknown, handled by default_parse_output) instead of
       spinning; per-query, not cumulative, so it fits the --incremental multi-
       check-sat usage. Full-saturation can run long, so this bounds it. *)
    [| ""; "--lang"; "smt2"; "--produce-models"; "--incremental"; "--strings-exp"; "--full-saturate-quant"; "--tlimit-per=120000"  |]

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

  let parse_output = default_parse_output

end



module ProverYices : Prover = struct
  let name = "Yices"

  let exec_paths =
    [ "/usr/local/bin/yices-smt2"
    ; "/opt/homebrew/bin/yices-smt2"
    ; "/usr/bin/yices-smt2"
    ]

  (* yices-smt2 reads SMT-LIB 2 from stdin; --incremental enables push/pop and
     interactive check-sat.  Models are emitted when the script sets
     (set-option :produce-models true). *)
  let args =
    [| ""; "--incremental" |]

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

  let parse_output = default_parse_output

end
