open Spec
open Smt
open Util


let rec find_ty (e: exp) (spec: spec) : ty option =
  match e with 
  | EVar (Var v) | EVar (VarPost v) | EVar (VarM (_, v)) -> 
      List.assoc_opt (Var v) spec.state
  | EFunc (str, expl) -> 
    begin match str with
    | "member" -> Some TBool
    | "union" -> begin match find_ty (List.hd expl) spec with Some ety -> Some (TSet ety) | None -> failwith "no type found" end
    | "str.len" -> Some TInt
    | "str.substr" -> Some TString
    | "str.++" -> Some TString
    | "str.contains" -> Some TBool
    | "insert" -> find_ty (List.hd @@ List.tl expl) spec
    | "select" -> begin match find_ty (List.hd expl) spec with Some (TArray (ty1,ty2)) -> Some ty2 | _ -> failwith "no type found" end
    | "store" -> find_ty (List.hd expl) spec
    | "singleton" -> find_ty (List.hd expl) spec
    | "setminus" -> find_ty (List.hd expl) spec
    | _ -> failwith ("this function is not defined: "^str)
    end
  | _ -> Some TInt

let generate_method_terms (spec: spec) (m: method_spec) : term_list list =
  (* let e = m.post in  *)
  (* let all_terms = ref [] in  *)
  let rec get_terms (e: exp) = 
    match e with 
    | EVar v -> 
      begin match v with
      | VarPost vp | VarM (_, vp) -> begin match find_ty (EVar (Var vp)) spec with | Some ety -> [(ety, EVar (Var vp))] | None -> [] end
      | Var _ -> begin match find_ty e spec with | Some ety -> [(ety, e)] | None -> [] end
      (* | VarM _ -> [] *)
      end
    | EArg _ -> [(TInt, e)] (* correct? *) 
    | EConst c ->
      begin match c with 
      | CInt i -> if i > 0 then [(TInt, EConst (CInt 0)); (TInt, EConst (CInt 1)); (TInt, e)] else [(TInt, e)]
      | CBool _ -> [(TBool, e)]
      | CString _ -> [(TString, e)]
      end
    | EBop (bop, exp1, exp2) -> 
      let t1 = get_terms exp1 in
      let t2 = get_terms exp2 in 
      begin match bop with 
      | Eq -> t1 @ t2
      | Lt | Gt | Lte | Gte -> (TBool, e) :: t1 @ t2
      | _ -> begin match find_ty exp1 spec with | Some ety -> (ety, e) :: t1 @ t2 | None -> t1 @ t2 end
      end
    | EUop (uop, exp) -> 
      let t = get_terms exp in
      begin match find_ty exp spec with | Some ety -> (ety, e) :: t | None -> t end
    | ELop (lop, expl) -> 
      let expl_terms = (List.concat_map get_terms expl) in
      begin match lop with 
      | Add -> begin match find_ty (List.hd expl) spec with | Some ety -> (ety, e) :: expl_terms | None -> expl_terms end
      | _ -> expl_terms
      end
      
    | ELet (expBindlist, exp) -> 
      let eb = List.concat_map (fun (var, ex) -> let vexp = EVar var in begin match find_ty vexp spec with | Some ety -> (ety, vexp) :: (get_terms ex) | None -> get_terms ex end) expBindlist in
      eb @ (get_terms exp)
    | EFunc (str, expl) -> 
      let expl_terms = (List.concat_map get_terms expl) in
      begin match find_ty e spec with | Some ety -> (ety, e) :: expl_terms | None -> expl_terms end 
    | EITE (e1, e2, e3) -> (get_terms e1) @ (get_terms e2)@ (get_terms e3)
    | _ -> []
  in 
  let method_terms = get_terms m.post @ get_terms m.pre @ (List.map (fun (var, ty) -> (ty, EVar var)) m.args) in 
  let unique_terms = Util.remove_duplicate method_terms in
  let terms = ref [] in
  List.iter (fun (ty, e) -> 
          let mem = List.find_opt (fun (typ, _) -> String.equal (string_of_ty ty) (string_of_ty typ)) !terms in
          begin match mem with
          | None -> terms := !terms @ [(ty, ref [e])] 
          | Some (t, mlist) -> mlist := !mlist @ [e]
          end
  ) unique_terms;
  List.map (fun (t, mlist) -> (t, !mlist)) !terms

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

let autogen_terms = ref false

let generate_predicates (spec: spec) (method1: method_spec) (method2: method_spec) =
  let type_terms = Hashtbl.create 2000 in

  let term_fn = if !autogen_terms then generate_method_terms spec else (fun x -> x.terms) in
  
  let mterms1 = term_fn method1 in
  let mterms2 = term_fn method2 in

  let all_terms = add_terms (add_terms type_terms mterms1) mterms2 in

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

  (* Printf.printf "%s\n" (ToMLString.list (string_of_pred) !pred_list); *)
  (* pred_list := add_manual_pred method2.post (add_manual_pred method1.post !pred_list); *)
  
  pfv "Preds: %s\n" @@ ToMLString.list (string_of_pred) !pred_list;

  !pred_list
