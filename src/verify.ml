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

let verify ?(options = default_verify_options) spec m n cond =
    
    let spec = if options.lift then lift spec else spec in
    
    let implication_function = if options.ncom
        then non_commute_of_smt spec
        else commute_of_smt spec
    in
    
    let m_spec = get_method spec m |> mangle_method_vars true in
    let n_spec = get_method spec n |> mangle_method_vars false in
    
    let init_time = Unix.gettimeofday () in
    
    seq (verif_time := Float.sub (Unix.gettimeofday ()) init_time) @@
    match solve options.prover spec m_spec n_spec [] (implication_function (ELop(And, [spec.precond; cond]))) with
        | Unsat -> Some true
        | Unknown -> None
        | Sat _ -> Some false
