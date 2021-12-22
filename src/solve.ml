(* Module for interfacing with theorem provers *)


open Util
open Smt
open Spec
open Provers


(* This will create the entire SMT string to send to a prover.
 * It will engage with lots of features of SMT which are
 * abstracted away from the actual "smt" module.
 * It'll include the variable declarations, function declarations, etc. *)
let smt_string_of_spec (spec : spec) (state_constraints : exp) : string =
  raise @@ Failure "smt_string_of_spec"


let solve (prover : (module Prover)) (spec : spec) (state_constraints : exp) : solve_result =
  let s = smt_string_of_spec spec state_constraints in
  let module P = (val prover) in
  P.run s
