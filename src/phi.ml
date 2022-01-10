open Smt

type atom = exp (* TODO: narrow this to just the kinds of atoms we want *)
let not_atom (a : atom) : atom = raise @@ Failure "not_atom"

type conjunction =
  Conj of atom list

let un_conj cs = match cs with Conj cs' -> cs'
let add_conjunct c cs = Conj (c :: un_conj cs)

type t = Disj of conjunction list



let un_disj ds = match ds with Disj ds' -> ds'
let add_disjunct d ds = Disj (d :: un_disj ds)

(* TODO: SMT expr. of conjunction and disjunction *)
let smt_of_conj (Conj al) =
  ELop (And, al)

let smt_of_disj (Disj cl) =
  ELop (Or, (List.map smt_of_conj cl))

let atom_of_pred (_ : Smt.pred) : atom = raise @@ Failure "atom_of_disj"

