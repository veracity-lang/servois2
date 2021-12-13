type atom = Smt.exp (* TODO: narrow this to just the kinds of atoms we want *)

type conjunction =
  Conj of atom list

type t = Disj of conjunction list

(* TODO: SMT expr. of conjunction and disjunction *)