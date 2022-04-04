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


let add_terms spec (type_terms) (tl: term_list list) =
  List.iter (fun (ty, el) -> 
    let rec process e = begin match e with
      | EVar (Var v) -> if List.mem (Var v) @@ List.map fst spec.state then [EVar (Var (v^"_l0")); EVar (Var (v^"_r0"))] else [EVar (Var v)]
      | EBop(b, el, er) -> let els = process el in let ers = process er in List.concat_map (fun el -> List.map (fun er -> EBop(b, el, er)) els) ers
      | EUop(u, e) -> List.map (fun e -> EUop(u, e)) @@ process e
      | ELop(lop, es) -> List.fold_right (fun e acc -> let es = process e in List.concat_map (fun e -> List.map (fun acce -> e::acce) acc) es) es [] |> List.map (fun es -> ELop(lop, es))
      | ELet(binds, e) -> List.map (fun e -> ELet(binds, e)) @@ process e (* TODO: Scope? *)
      | EITE(i, t, e) -> let is = process i in let ts = process t in let es = process e in List.concat_map (fun i -> List.concat_map (fun t -> List.map (fun e -> EITE(i, t, e)) es) ts) is
      | EFunc(s, es) -> List.fold_right (fun e acc -> let es = process e in List.concat_map (fun e -> List.map (fun acce -> e::acce) acc) es) es [] |> List.map (fun es -> EFunc(s, es))
      | x -> [x] end in
    let el' = List.concat_map process el in
    match Hashtbl.find_opt type_terms ty with 
    | Some t -> Hashtbl.replace type_terms ty (el' @ t)
    | None -> Hashtbl.add type_terms ty el'
  ) tl;
  type_terms

let generate_predicates (spec: spec) (method1: method_spec) (method2: method_spec) : pred list =
  let type_terms = Hashtbl.create 100 in

  let all_terms = add_terms spec (add_terms spec type_terms method1.terms) method2.terms in

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
  
  pfv "Preds: %s\n" @@ ToMLString.list (string_of_pred) !pred_list;

  !pred_list
