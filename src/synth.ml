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

type counterex = exp bindlist

let prover : (module Prover) = (module ProverCVC4)

let remove (x : 'a) : 'a list -> 'a list = List.filter (fun x' -> x' != x)

let synth ?(preds = []) (spec : spec) (m : string) (n : string) : Phi.t * Phi.t =
  let phi = ref @@ Disj [] in
  let phi_tilde = ref @@ Disj [] in
  let spec_lifted = lift spec in
  let m_spec = get_method spec_lifted m in
  let n_spec = get_method spec_lifted n in
  let preds = if null preds then generate_predicates spec_lifted m_spec n_spec else preds in
  let rec refine (h : conjunction) (p_set : pred list) : unit =
    let solve_inst = solve prover spec_lifted m_spec n_spec in
    let pred_smt = List.map smt_of_pred p_set in
    begin match solve_inst pred_smt @@ commute h with
      | Unsat -> phi := add_disjunct h !phi
      | Unknown -> raise @@ Failure "commute failure" (* TODO: Better error behavior? Backtracking? *)
      | Sat s -> begin let com_cex = parse_pred_data s in
        match solve_inst pred_smt @@ non_commute h with
          | Unsat -> phi_tilde := add_disjunct h !phi_tilde
          | Unknown -> raise @@ Failure "non_commute failure"
          | Sat s -> begin let non_com_cex = parse_pred_data s in
            let p = !choose solve_inst h p_set com_cex non_com_cex in
                refine (add_conjunct (atom_of_pred p) h) (remove p p_set);
                refine (add_conjunct (not_atom @@ atom_of_pred p) h) (remove p p_set)
            end
        end
    end in
  begin try refine (Conj []) (List.sort (fun x y -> complexity x - complexity y) @@ preds) 
      with | Failure f -> print_string f; print_newline ()
  end;
  !phi, !phi_tilde
