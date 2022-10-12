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
    let s1, s2 = Smt_ToMLString.exp exp1, Smt_ToMLString.exp exp2 in
    String.compare s1 s2 >= 0 &&
    List.exists (fun (o,e1,e2) -> 
        (String.equal o op) && (String.equal s1 (Smt_ToMLString.exp e2)) 
        && (String.equal s2 (Smt_ToMLString.exp e1))
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

(* let add_manual_pred (pc: exp) (pl: pred list) : pred list = 
  match pc with 
  | EITE (e, _, _) -> 
    begin match e with
    | EBop (bop, e1, e2)

    end 
  | _ -> pl
  pl *)

let rec add_manual_pred (pc: exp) (pl: pred list) : pred list =
  match pc with
  | EITE (e1, _, _) -> (add_manual_pred e1 pl)
  | EBop (bop, e1, e2) -> 
    let bStr = begin match bop with
    (* | Eq  -> "=" *)
    | Lt  -> "<"
    | Gt  -> ">"
    | Lte -> "<="
    | Gte -> ">="
    | _ -> ""
    end in
    if (not (String.equal "" bStr)) && (not (List.mem (bStr, e1, e2) pl)) then begin 
      let p1 = add_manual_pred e1 pl in 
      let p2 = add_manual_pred e2 p1 in
      (bStr, e1, e2) :: p2
      end 
    else 
      pl
  | ELop (lop, expl) -> List.fold_left (fun plist -> fun exp -> add_manual_pred exp plist) pl expl
  | _ -> pl


let generate_predicates (spec: spec) (method1: method_spec) (method2: method_spec) : pred list =
  let type_terms = Hashtbl.create 100 in

  let all_terms = add_terms (add_terms type_terms method1.terms) method2.terms in

  let pred_list = ref [] in
  List.iter (fun [@warning "-8"] (PredSig (name,[ty1;ty2])) ->
    match (Hashtbl.find_opt all_terms ty1), (Hashtbl.find_opt all_terms ty2) with
    | None, _ | _, None -> ()
    | Some ty1_terms, Some ty2_terms ->  
    iter_prod (fun left right ->
        if not (List.mem (name,left,right) !pred_list ||
          is_reflx name left right ||
          is_symm name left right !pred_list ||
          is_const name left right )
        then pred_list := (name,left,right) :: !pred_list
    ) (Hashtbl.find all_terms ty1) (Hashtbl.find all_terms ty2)
  ) spec.preds;

  Printf.printf "=============== size: %d\n" (List.length !pred_list);
  Printf.printf "%s\n" (ToMLString.list (string_of_pred) !pred_list);

  pred_list := add_manual_pred method2.post (add_manual_pred method1.post !pred_list);
  
  pfv "Preds: %s\n" @@ ToMLString.list (string_of_pred) !pred_list;

  Printf.printf "=============== size: %d\n" (List.length !pred_list);
  Printf.printf "%s\n" (ToMLString.list (string_of_pred) !pred_list);
  !pred_list

(* 
let add_pred (p: pred) (pl: pred list) : pred list =
  if (not (List.mem p pred_list)) (* TODO: filtering  *) then
    (p :: pl)

let extract_pred (e: exp) (pl: pred list) : pred list = 
  match e with
  | EVar var -> 
  | EArg of int
  | EConst of const
  | EBop (bop, exp1, exp2) -> 
    ((string_of_bop bop), exp1, exp2) ::
    extract_pred exp1 pl @
    extract_pred exp2 pl 
  | EUop of uop * exp
  | ELop of lop * exp list

let generate_predicates2 (spec: spec) (method1: method_spec) (method2: method_spec) : pred list =
  let post1 = method1.post in 
  let post2 = method2.post in 
  let pred_list = ref [] in
  extract_pred post2 (extract_pred post1 pred_list) *)
