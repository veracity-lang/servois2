open Spec
open Smt

(* let f l1 l2 = 
   let res = List.fold_left (fun acc x ->
     List.fold_left (fun acc y -> (x * y) :: acc) acc l2
   ) [] l1 in
   List.rev res *)
  
type pred = string * exp * exp

let add_terms (type_terms) (tl: term_list list) =
  List.iter (fun (ty, el) -> 
    match Hashtbl.find_opt type_terms ty with 
    | Some t -> Hashtbl.replace type_terms ty (el @ t)
    | None -> Hashtbl.add type_terms ty el
  ) tl;
  type_terms

let generate_predicates (spec: spec) (m1: string) (m2: string) : pred list =
  
  let type_terms = Hashtbl.create 100 in

  let method1 = List.find (fun (m: method_spec) -> String.equal m.name m1) spec.methods in
  let method2 = List.find (fun (m: method_spec) -> String.equal m.name m2) spec.methods in 
  (* let all_terms = List.merge (fun (ty1, el1) (ty2, el2) -> ty1 == ty2) method1.terms method2.terms in
    *)
  let all_terms = add_terms (add_terms type_terms method1.terms) method2.terms in

  let pred_list = ref [] in
  List.iter (fun (Pred (name,tys)) ->
    let ty1 = List.nth tys 0 in
    let ty2 = List.nth tys 1 in
    let left = List.hd (Hashtbl.find all_terms ty1) in
    Hashtbl.replace all_terms ty1 (List.tl (Hashtbl.find all_terms ty1));
    let right = List.hd (Hashtbl.find all_terms ty2) in
    Hashtbl.replace all_terms ty2 (List.tl (Hashtbl.find all_terms ty2));

    pred_list := (name,left,right) :: !pred_list
  ) spec.preds;

  !pred_list