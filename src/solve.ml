open Util
open Smt
open Spec

(* TODO *)
type solve_result =
  | Valid
  | Invalid
  | Failure


(* We instantiate the module with specific provers, e.g. CVC4, Z3 *)
module type Prover = sig
  val run : string -> solve_result
end

let smt_string_of_spec (spec : spec) (state_constraints : exp) : string =
  raise @@ NotImplemented "smt_string_of_spec"

let solve (prover : (module Prover)) (spec : spec) (state_constraints : exp) : solve_result =
  let s = smt_string_of_spec spec state_constraints in
  let module P = (val prover) in
  P.run s