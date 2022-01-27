open Smt
open Util

let differentiating_predicates (ps : pred list) (a : bool list) b : (pred list) =
    (* TODO: Account for a/b not being simple true/false *)
    List.fold_right2 (fun pred incl acc -> if incl then pred :: acc else acc) ps (List.map2 (fun x y -> x != y) a b) []

let rec size = function
  | EVar _ -> 1
  | EConst _ -> 1
  | EBop(_, e1, e2) -> 1 + size e1 + size e2
  | EUop(_, e) -> 1 + size e
  | ELop(_, es) -> 1 + list_sum (List.map size es)
  | ELet(_, e) -> 1 + size e
  | EITE(e1, e2, e3) -> 1 + size e1 + size e2 + size e3
  | EFunc(_, es) -> 1 + list_sum (List.map size es)

let complexity = memoize @@ fun (_, left, right) -> size left + size right

let choose h ps com n_com : pred =
    let diff_preds = differentiating_predicates ps com n_com in
    print_string (ToMLString.list string_of_pred diff_preds);
    list_min complexity diff_preds

