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

type counterex = exp bindlist

let prover : (module Prover) = (module ProverCVC4)

let remove (x : 'a) : 'a list -> 'a list = List.filter (fun x' -> x' != x)

let bool_of_exp = function (* TODO *)
    | EConst(CBool t) -> t
    | _ -> failwith "bool_of_exp"

let parse_pred_data = compose (List.map (compose bool_of_exp snd)) values_of_string

let non_commute h = EBop(Imp, smt_of_conj @@ (add_conjunct smt_oper h), EUop(Not, smt_bowtie))
let commute h = EBop(Imp, smt_of_conj @@ (add_conjunct smt_oper h), smt_bowtie)

let synth (spec : spec) (m : string) (n : string) : Phi.t * Phi.t =
  let phi = ref @@ Disj [] in
  let phi_tilde = ref @@ Disj [] in
  let spec_lifted = lift spec in
  let m_spec = get_method spec_lifted m in
  let n_spec = get_method spec_lifted n in
  let rec refine (h : conjunction) (p_set : pred list) : unit =
    let solve_inst = solve prover spec_lifted m_spec n_spec (List.map smt_of_pred p_set) in
    begin match solve_inst @@ commute h with
      | Unsat -> phi := add_disjunct h !phi
      | Unknown -> raise @@ Failure "commute failure" (* TODO: Better error behavior? Backtracking? *)
      | Sat s -> begin let com_cex = parse_pred_data s in
        match solve_inst @@ non_commute h with
          | Unsat -> phi_tilde := add_disjunct h !phi_tilde
          | Unknown -> raise @@ Failure "non_commute failure"
          | Sat s -> begin let non_com_cex = parse_pred_data s in
            let p = choose h p_set com_cex non_com_cex in
                refine (add_conjunct (atom_of_pred p) h) (remove p p_set);
                refine (add_conjunct (not_atom @@ atom_of_pred p) h) (remove p p_set)
            end
        end
    end in
  begin try refine (Conj []) (Predicate.generate_predicates spec m_spec n_spec) 
      with | Failure f -> print_string f; print_newline ()
  end;
  !phi, !phi_tilde
