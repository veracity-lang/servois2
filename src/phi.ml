open Smt

type atom = exp (* TODO: narrow this to just the kinds of atoms we want *)
let not_atom = function 
    | EUop(Not, a) -> a
    | a -> EUop(Not, a)

type conjunction =
  Conj of atom list

let un_conj cs = match cs with Conj cs' -> cs'
let add_conjunct c cs = Conj (c :: un_conj cs)

type t = Disj of conjunction list



let un_disj ds = match ds with Disj ds' -> ds'
let add_disjunct d ds = Disj (d :: un_disj ds)

(* TODO: SMT expr. of conjunction and disjunction *)
let smt_of_conj = function
  | Conj [] -> EConst (CBool true)
  | Conj (x :: []) -> x
  | Conj al -> ELop (And, al)

let smt_of_disj = function
  | Disj [] -> EConst(CBool false)
  | Disj (x :: []) -> smt_of_conj x
  | Disj cl -> ELop (Or, (List.map smt_of_conj cl))
let string_of_disj d = smt_of_disj d |> string_of_smt

let atom_of_pred ((f, e1, e2) : Smt.pred) : atom = EFunc(f, [e1; e2])

module ToString = struct
  let t = string_of_disj
end
