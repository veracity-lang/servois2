(* Module for conducting the phi synthesis algorithm 
 * Algorithm comes from Fig. 1 of TACAS'18.
 *)

open Util
open Smt
open Solve
open Spec
open Phi
open Provers

type counterex = exp bindlist

let prover : (module Prover) = (module ProverCVC4)

let non_commute _ = raise @@ Failure "non_commute"
let commute h spec m n = EForAll(spec.state @ m.ret @ m.args @ n.ret @ n.args, EBop(Imp, h (* of parameters ?? *), (* TODO *) m.post))

(* TODO *)
let choose _ ps _ _ = List.hd ps (* raise @@ Failure "choose" *)

let remove (x : 'a) : 'a list -> 'a list = List.filter (fun x' -> x' != x)



let synth (spec : spec) (m : string) (n : string) : Phi.t * Phi.t =
  let phi = ref @@ Disj [] in
  let phi_tilde = ref @@ Disj [] in
  let m_spec = get_method spec m in
  let n_spec = get_method spec n in
  let rec refine (h : conjunction) (p_set : pred list) : unit =
    begin match solve prover spec @@ commute (smt_of_conj h) spec m_spec n_spec with
      | Sat -> phi := add_disjunct h !phi
      | Unknown -> raise @@ Failure "commute failure" (* TODO: Better error behavior? Backtracking? *)
      | Unsat s -> begin let com_cex = s in
        match solve prover spec (EBop(Imp, smt_of_conj h, non_commute m_spec n_spec)) with
          | Sat -> phi_tilde := add_disjunct h !phi_tilde
          | Unknown -> raise @@ Failure "non_commute failure"
          | Unsat s -> begin let non_com_cex = s in
            let p = choose h p_set com_cex non_com_cex in
                refine (add_conjunct (atom_of_pred p) h) (remove p p_set);
                refine (add_conjunct (not_atom @@ atom_of_pred p) h) (remove p p_set)
            end
        end
    end in
  begin try refine (Conj []) []
      with | Failure f -> print_string f; print_newline ()
  end;
  !phi, !phi_tilde
