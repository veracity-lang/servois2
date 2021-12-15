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

let prover : (module Prover) = raise @@ Failure "prover"

let non_commute = raise @@ Failure "non_commute"
let commute = raise @@ Failure "commute"
let choose = raise @@ Failure "choose"

let remove (x : 'a) (xs : 'a list) : 'a list = raise @@ Failure "choose"


let synth (spec : spec) (m : string) (n : string) : Phi.t * Phi.t =
  let phi = ref @@ Disj [] in
  let phi_tilde = ref @@ Disj [] in
  let rec refine (h : conjunction) (p_set : pred list) : unit =
    begin match solve prover spec (EBop(Imp, exp_of_conj h, commute (get_method spec m) (get_method spec n))) with
      | Valid -> phi := add_disjunct h !phi
      | Unknown -> raise @@ Failure "commute failure"
      | Invalid s -> begin let com_cex = s in
        match solve prover spec (EBop(Imp, exp_of_conj h, non_commute (get_method spec m) (get_method spec n))) with
          | Valid -> phi_tilde := add_disjunct h !phi_tilde
          | Unknown -> raise @@ Failure "non_commute failute"
          | Invalid s -> begin let non_com_cex = s in
            let p = choose h p_set com_cex non_com_cex in
                refine (add_conjunct (atom_of_pred p) h) (remove p p_set);
                refine (add_conjunct (not_atom @@ atom_of_pred p) h) (remove p p_set)
            end
        end
    end in
  begin try refine (Conj []) []
      with | _ -> ()
  end;
  !phi, !phi_tilde
