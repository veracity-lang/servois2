open Smt

type atom = exp (* TODO: narrow this to just the kinds of atoms we want *)
let not_atom = function 
    | EUop(Not, a) -> a
    | a -> EUop(Not, a)

type conjunction =
  Conj of atom list

let un_conj cs = match cs with Conj cs' -> cs'
let add_conjunct c cs = match c with
    | EConst (CBool true) -> cs
    | _ -> Conj (c :: un_conj cs)

type disjunction = Disj of conjunction list
type t = disjunction

let un_disj ds = match ds with Disj ds' -> ds'
let add_disjunct d ds = match d with
    | Conj [] -> begin match ds with | Disj [] -> Disj [Conj []] | _ -> ds end
    | _ -> Disj (d :: un_disj ds)

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

let predP_of_atom : atom -> predP option = 
  fun e -> 
  match e with
  | EFunc (f, [e1; e2]) ->Some (P (f, e1, e2))
  | EBop (o, e1, e2) -> 
    begin match o with
      | (Imp | Eq | Lt | Gt | Lte | Gte ) -> Some (P (To_String.bop o, e1, e2))
      | _ -> None
    end
  | EUop (Not, EFunc (f, [e1; e2])) -> Some (NotP (f, e1, e2))
  | EUop (Not, EBop (o, e1, e2)) -> 
    begin match o with
      | (Imp | Eq | Lt | Gt | Lte | Gte ) -> Some (NotP (To_String.bop o, e1, e2))
      | _ -> None
    end
  | _ -> None  

let atom_of_predP = function
  | P p -> atom_of_pred p
  | NotP p -> EUop (Not, atom_of_pred p)

module ToString = struct
  let t = string_of_disj
end

let n_atoms_of : t -> int = Util.compose (List.fold_left (fun acc conj -> acc + List.length (un_conj conj)) 0) un_disj

