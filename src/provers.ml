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

(* Extra CVC5 command-line flags supplied by the embedder, read per query so it
   can be set at runtime (e.g. ConQuoer enables --full-saturate-quant only for
   benchmarks with 2-D arrays, whose -ae store-vs-havoc goals need it). Applies
   to the CVC5 prover only. *)
let cvc5_extra_args : string list ref = ref []


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
    let args =
      if P.name = "CVC5" && !cvc5_extra_args <> []
      then Array.append P.args (Array.of_list !cvc5_extra_args)
      else P.args
    in
    (* The per-query limit is not baked into P.args: it comes from the shared
       Timeouts record, so every layer above can configure it. *)
    let args = Array.append args (Timeouts.prover_args P.name) in
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
    [| ""; "--lang"; "smt2"; "--produce-models"; "--incremental"; "--fmf-fun"; "--strings-exp" |]

  let parse_output = default_parse_output

end



module ProverCVC5 : Prover = struct
  let name = "CVC5"

  let exec_paths =
    [ "/usr/local/bin/cvc5"
    ; "/usr/bin/cvc5"
    ; "/opt/homebrew/bin/cvc5"
    ]

  let args =
    (* The per-check-sat limit (--tlimit-per) is appended by run_prover from
       Timeouts.prover_args, so it can be configured from any layer above.
       --full-saturate-quant is NOT set here unconditionally — it slows some
       benchmarks. It is added per-run via [cvc5_extra_args] (see run_prover)
       only when the embedder requests it (ConQuoer: benchmarks with 2-D
       arrays, whose -ae store-vs-havoc goals need full-saturation to close). *)
    [| ""; "--lang"; "smt2"; "--produce-models"; "--incremental"; "--strings-exp" |]

  let parse_output = default_parse_output

end


module ProverZ3 : Prover = struct
  let name = "Z3"

  let exec_paths =
    [ "/usr/local/bin/z3"
    ; "/usr/bin/z3"
    ; "/opt/homebrew/bin/z3"
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
