open Smt

type atom = exp (* TODO: narrow this to just the kinds of atoms we want *)

type conjunction =
  Conj of atom list

type t = Disj of conjunction list

let smt_of_conj (Conj al) =
  ELop (And, al)

let smt_of_phi (Disj cl) =
  ELop (Or, (List.map smt_of_conj cl))