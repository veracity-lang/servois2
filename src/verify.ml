open Solve
open Spec
open Provers
open Util

type verify_options =
  { prover : (module Prover)
  ; lift : bool
  ; ncom : bool
  }

let default_verify_options =
  { prover = (module Provers.ProverCVC4)
  ; lift = true
  ; ncom = false
  }

let verif_time = ref 0.0

let verify ?(options = default_verify_options) spec ms ns cond =
    
    let spec = if options.lift then lift spec else spec in
    
    let implication_function = if options.ncom
        then non_commute_of_smt
        else commute_of_smt
    in
    
    let ms_specs = List.map (compose (mangle_method_vars true) (get_method spec)) ms in
    let ns_specs = List.map (compose (mangle_method_vars false) (get_method spec)) ns in
    
    let init_time = Unix.gettimeofday () in
    
    seq (verif_time := Float.sub (Unix.gettimeofday ()) init_time) @@
    match solve options.prover spec ms_specs ns_specs [] (implication_function (ELop(And, [spec.precond; cond]))) with
        | Unsat -> Some true
        | Unknown -> None
        | Sat _ -> Some false
