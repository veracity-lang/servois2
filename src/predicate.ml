open Spec
open Smt
open Util

let is_reflx (op: string) (exp1: exp) (exp2: exp) : bool =
  match op with
  | "=" -> 
    if String.equal (Smt_ToMLString.exp exp1) (Smt_ToMLString.exp exp2) then
      true
    else 
      false
  | _ -> false


let is_symm (op: string) (exp1: exp) (exp2: exp) =
  function preds_list ->
  match op with
  | "=" -> 
    List.exists (fun (o,e1,e2) -> 
        (String.equal o op) && (String.equal (Smt_ToMLString.exp exp1) (Smt_ToMLString.exp e2)) 
        && (String.equal (Smt_ToMLString.exp exp2) (Smt_ToMLString.exp e1))
    ) preds_list

  | _ -> false


let is_const (op: string) (exp1: exp) (exp2: exp) =
  match op with
  | "=" | ">" -> begin match exp1, exp2 with
                | EConst _, EConst _  -> true
                | _ -> false
                end
  | _ -> false


let add_terms (type_terms) (tl: term_list list) =
  List.iter (fun (ty, el) -> 
    match Hashtbl.find_opt type_terms ty with 
    | Some t -> Hashtbl.replace type_terms ty (el @ t)
    | None -> Hashtbl.add type_terms ty el
  ) tl;
  type_terms

let generate_predicates (spec: spec) (method1: method_spec) (method2: method_spec) : pred list =
  let type_terms = Hashtbl.create 100 in

  let all_terms = add_terms (add_terms type_terms method1.terms) method2.terms in

  let pred_list = ref [] in
  List.iter (fun [@warning "-8"] (PredSig (name,[ty1;ty2])) ->
    match (Hashtbl.find_opt all_terms ty1), (Hashtbl.find_opt all_terms ty2) with
    | None, _ | _, None -> ()
    | Some ty1_terms, Some ty2_terms ->  
    List.iter (
      fun left ->
      List.iter (
        fun right -> 
          if not (List.mem (name,left,right) !pred_list) then
            if not (is_reflx name left right) then
              if not (is_symm name left right !pred_list) then
                if not (is_const name left right) then
                  pred_list := (name,left,right) :: !pred_list
      ) (Hashtbl.find all_terms ty2)
    ) (Hashtbl.find all_terms ty1)
  ) spec.preds;
  
  pfv "Preds: %s\n" @@ ToMLString.list (string_of_pred) !pred_list;

  !pred_list
