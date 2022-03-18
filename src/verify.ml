open Solve
open Spec
open Provers

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

let verify ?(options = default_verify_options) spec m n cond =
    
    let spec = if options.lift then lift spec else spec in
    
    let implication_function = if options.ncom
        then non_commute_of_smt
        else commute_of_smt
    in
    
    let m_spec = get_method spec m |> mangle_method_vars true in
    let n_spec = get_method spec n |> mangle_method_vars false in
    
    match solve options.prover spec m_spec n_spec [] (implication_function (ELop(And, [spec.precond; cond]))) with
        | Unsat -> Some true
        | Unknown -> None
        | Sat _ -> Some false
