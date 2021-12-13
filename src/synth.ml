(* Module for conducting the phi synthesis algorithm 
 * Algorithm comes from Fig. 1 of TACAS'18.
 *)

open Util
open Smt
open Solve
open Spec
open Phi

type counterex = exp bindlist


(*




*)

let prover : (module Prover) = raise @@ NotImplemented "prover"

let refine phi phi_tilde (h : conjunction) (p : pred list) : unit =
  (*match solve prover *)
  raise @@ NotImplemented "refine"


let synth (spec : spec) (m : string) (n : string) : Phi.t * Phi.t =
  let phi = ref @@ Disj [] in
  let phi_tilde = ref @@ Disj [] in
  refine phi phi_tilde (Conj []) [];
  !phi, !phi_tilde