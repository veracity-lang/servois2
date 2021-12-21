type atom = Smt.exp (* TODO: narrow this to just the kinds of atoms we want *)
let not_atom (a : atom) : atom = raise @@ Failure "not_atom"

type conjunction =
  Conj of atom list

let un_conj cs = match cs with Conj cs' -> cs'
let add_conjunct c cs = Conj (c :: un_conj cs)

type t = Disj of conjunction list

let un_disj ds = match ds with Disj ds' -> ds'
let add_disjunct d ds = Disj (d :: un_disj ds)

(* TODO: SMT expr. of conjunction and disjunction *)
let exp_of_conj : conjunction -> Smt.exp = raise @@ Failure "exp_of_disj"
let exp_of_disj : t -> Smt.exp = raise @@ Failure "exp_of_disj"
let atom_of_pred : Smt.pred -> atom = raise @@ Failure "atom_of_disj"
