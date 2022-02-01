open Smt
open Util
open Solve
open Provers
open Phi

let differentiating_predicates (ps : pred list) (a : bool list) b : ((pred * bool) list) = (* The bool should be true if the predicate is true in the commute (first list) case *)
    (* TODO: Account for a/b not being simple true/false *)
    List.fold_right2 (fun pred (x, y) acc -> if (x != y) then (pred, x) :: acc else acc) ps (List.map2 (fun x y -> (x, y)) a b) []

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

let simple h ps com n_com : pred =
    let diff_preds = List.map fst @@ differentiating_predicates ps com n_com in
    list_min int_comp complexity diff_preds

let poke solver h ps com n_com : pred =
    let next = differentiating_predicates ps com n_com in
    let diff_preds = List.map fst next in
    let smt_diff_preds = List.map smt_of_pred diff_preds in
    fst @@ list_min lex_comp (fun (p, cov) -> 
    (let h' = add_conjunct ((if cov then id else not_atom) @@ atom_of_pred p) h in
    let h'' = add_conjunct ((if cov then not_atom else id) @@ atom_of_pred p) h in
    match solver smt_diff_preds @@ commute h' with (* TODO: Possibly cache these results as synth also uses them? *)
      | Unsat -> -1
      | Unknown -> max_int (* TODO: Better way to encode this? *)
      | Sat s -> begin let com_cex = parse_pred_data s in
        match solver smt_diff_preds @@ non_commute h'' with
          | Unsat -> -1
          | Unknown -> max_int
          | Sat s -> begin let non_com_cex = parse_pred_data s in
            List.length (differentiating_predicates diff_preds com_cex non_com_cex)
            end
        end
    ), complexity p) next

let choose = simple
