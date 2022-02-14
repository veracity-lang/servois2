(* Module for conducting the phi synthesis algorithm 
 * Algorithm comes from Fig. 1 of TACAS'18.
 *)

open Util
open Smt
open Solve
open Spec
open Phi
open Provers
open Choose
open Smt_parsing
open Predicate

type synth_options = 
  { preds : pred list option
  ; prover : (module Prover)
  ; lift : bool
  ; timeout : float option
  }

let default_synth_options =
  { preds = None
  ; prover = (module Provers.ProverCVC4)
  ; lift = true
  ; timeout = None
  }

type counterex = exp bindlist

let remove (x : 'a) : 'a list -> 'a list = List.filter (fun x' -> x' != x)

let synth ?(options = default_synth_options) spec m n =
    let synth_inner preds prover spec m_spec n_spec = 
      let phi = ref @@ Disj [] in
      let phi_tilde = ref @@ Disj [] in
      let rec refine (h : conjunction) (p_set : pred list) : unit =
        let solve_inst = solve prover spec m_spec n_spec in
        let pred_smt = List.map smt_of_pred p_set in
        begin match solve_inst pred_smt @@ commute (spec.precond) h with
          | Unsat -> phi := add_disjunct h !phi
          | Unknown -> raise @@ Failure "commute failure" (* TODO: Better error behavior? Backtracking? *)
          | Sat s -> begin let com_cex = parse_pred_data s in
            match solve_inst pred_smt @@ non_commute (spec.precond) h with
              | Unsat -> phi_tilde := add_disjunct h !phi_tilde
              | Unknown -> raise @@ Failure "non_commute failure"
              | Sat s -> begin let non_com_cex = parse_pred_data s in
                let p = !choose { solver = solve_inst; spec = spec; h = h; choose_from = p_set; cex_ncex = (com_cex, non_com_cex) } in
                    refine (add_conjunct (atom_of_pred p) h) (remove p p_set);
                    refine (add_conjunct (not_atom @@ atom_of_pred p) h) (remove p p_set)
                end
            end
        end in
      begin try refine (Conj []) (List.sort (fun x y -> complexity x - complexity y) @@ preds) 
          with | Failure f -> print_string f; print_newline ()
      end;
      !phi, !phi_tilde in
    let spec' = if options.lift then lift spec else spec in
    let m_spec = get_method spec m in
    let n_spec = get_method spec n in
    let preds = match options.preds with None -> generate_predicates spec' m_spec n_spec | Some x -> x in
    synth_inner preds options.prover spec' m_spec n_spec
  
