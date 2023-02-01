open Spec
open Smt
open Util

let replace input output =
  Str.global_replace (Str.regexp_string input) output

let rec last lst =
  match lst with
  | [] -> failwith "Empty list"
  | [x] -> x
  | hd::tl -> last tl

let remove_index (mangled_id: string) : string =
  let r = Str.regexp "_[0-9]+" in 
  Str.replace_first r "" mangled_id
  
let rec remove_index_exp (e: exp) : exp = 
  match e with 
  | EVar (Var v) -> EVar (Var (remove_index v))
  | EVar (VarPost v) -> EVar (VarPost (remove_index v))
  | EVar (VarM (m, v)) -> EVar (VarM (m, (remove_index v)))
  | EFunc (str, expl) -> 
    let new_expl = List.map remove_index_exp expl in
    EFunc (str, new_expl)
  | EBop (bop, exp1, exp2) -> 
    let new_exp1 = remove_index_exp exp1 in
    let new_exp2 = remove_index_exp exp2 in
    EBop (bop, new_exp1, new_exp2)
  | EUop (uop, exp) -> 
    let new_exp = remove_index_exp exp in
    EUop (uop, new_exp)
  | ELop (lop, expl) -> 
    let new_expl = List.map remove_index_exp expl in
    ELop (lop, new_expl)
  | ELet (expBindlist, exp) -> 
    let eb = List.map (fun (var, ex) -> let [@warning "-8"] EVar v = remove_index_exp (EVar var) in (v , remove_index_exp ex)) expBindlist in
    let new_exp = remove_index_exp exp in 
    ELet (eb, new_exp)
  | EITE (exp1, exp2, exp3) -> 
    let new_exp1 = remove_index_exp exp1 in
    let new_exp2 = remove_index_exp exp2 in
    let new_exp3 = remove_index_exp exp3 in
    EITE (new_exp1, new_exp2, new_exp3)
  | _ -> e
  
let rec find_ty (e: exp) (spec: spec) : ty option =
  match e with 
  | EVar (Var v) | EVar (VarPost v) | EVar (VarM (_, v)) -> 
      (* List.assoc_opt (Var v) spec.state *)
      begin match List.assoc_opt (Var v) spec.state with
      | None -> let str = remove_index v in List.assoc_opt (Var str) spec.state
      | x -> x
      end
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
  let rec get_terms (e: exp) = 
    match e with 
    | EVar v -> 
      begin match v with
      | VarPost vp | VarM (_, vp) | Var vp -> let str = remove_index vp in begin match find_ty (EVar (Var str)) spec with | Some ety -> [(ety, EVar (Var str))] | None -> [] end
      end
    | EArg _ -> [(TInt, remove_index_exp e)]
    | EConst c ->
      begin match c with 
      | CInt i -> if i > 0 then [(TInt, EConst (CInt 0)); (TInt, EConst (CInt 1)); (TInt, e)] else [(TInt, e)]
      | CBool _ -> [(TBool, e)]
      | CString _ -> [(TString, e)]
      | CBitVector v -> [(TBitVector (List.length v), e)]
      end
    | EBop (bop, exp1, exp2) -> 
      let t1 = get_terms exp1 in
      let t2 = get_terms exp2 in 
      begin match bop with 
      | Eq -> t1 @ t2
      | Lt | Gt | Lte | Gte -> (TBool, remove_index_exp e) :: t1 @ t2
      | _ -> begin match find_ty exp1 spec with | Some ety -> (ety, remove_index_exp e) :: t1 @ t2 | None -> t1 @ t2 end
      end
    | EUop (uop, exp) -> 
      let t = get_terms exp in
      begin match find_ty exp spec with | Some ety -> (ety, remove_index_exp e) :: t | None -> t end
    | ELop (lop, expl) -> 
      let expl_terms = (List.concat_map get_terms expl) in
      begin match lop with 
      | Add -> begin match find_ty (List.hd expl) spec with | Some ety -> (ety, remove_index_exp e) :: expl_terms | None -> expl_terms end
      | _ -> expl_terms
      end
      
    | ELet (expBindlist, exp) -> 
      let eb = List.concat_map (fun (var, ex) -> let vexp = EVar var in begin match find_ty vexp spec with | Some ety -> (ety, remove_index_exp vexp) :: (get_terms ex) | None -> get_terms ex end) expBindlist in
      eb @ (get_terms exp)
    | EFunc (str, expl) -> 
      let expl_terms = (List.concat_map get_terms expl) in
      begin match find_ty e spec with | Some ety -> (ety, remove_index_exp e) :: expl_terms | None -> expl_terms end 
    | EITE (e1, e2, e3) -> (get_terms e1) @ (get_terms e2)@ (get_terms e3)
    | _ -> []
  in 
  let method_terms = get_terms m.post @ get_terms m.pre @ (List.map (fun (var, ty) -> (ty, remove_index_exp(EVar var) )) m.args) in 
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

let default_fns =
  [ {name = "+" ; args = [TInt; TInt] ; ret = TInt}
  ; {name = "*" ; args = [TInt; TInt] ; ret = TInt}
  (* ; {name = "mod" ; args = [TInt; TInt] ; ret = TInt} -- mod omitted for issues with cvc4. *)
  
  ; {name = "member" ; args = [TSet (TGeneric "E"); TGeneric "E"] ; ret = TBool}
  ; {name = "union" ; args = [TSet (TGeneric "E"); TSet (TGeneric "E")] ; ret = TSet (TGeneric "E")}
  ; {name = "setminus" ; args = [TSet (TGeneric "E"); TSet (TGeneric "E")] ; ret = TSet (TGeneric "E")}
  ; {name = "singleton" ; args = [TGeneric "E"] ; ret = TSet (TGeneric "E")}
  
  ; {name = "select" ; args = [TArray (TGeneric "E", TGeneric "F"); TGeneric "E"] ; ret = TGeneric "F"}
  ; {name = "store" ; args = [TArray (TGeneric "E", TGeneric "F"); TGeneric "E"; TGeneric "F"] ; ret = TArray (TGeneric "E", TGeneric "F")}
  
  ]


let rec sygus_terms (terms : term_list list) (fns : smt_fn list) (depth : int) : term_list list =
  if depth = 0
  then terms
  else let lookup  = fun k -> assoc_default k terms [] in 
       let terms' = List.fold_left (fun terms_acc (smt_fn : smt_fn) ->
         let res_list = lookup smt_fn.ret in
         let args_lists = List.fold_right (fun arg_ty args_lists -> (* Create all possible args lists *)
           (* do term <- lookup arg_ty; args_list <- args_lists; return (term : args_list) *)
           flip List.concat_map (lookup arg_ty) (fun term ->
           flip List.map args_lists (fun args_list -> term :: args_list
           ))
         ) smt_fn.args [[]] in
         (* From each construct a new expression and add it as a term *)
         flip (assoc_update smt_fn.ret) terms_acc @@ concat_unique (List.map (fun args_list ->
           EFunc(smt_fn.name, args_list)) args_lists) res_list
       ) terms fns in
       sygus_terms terms' fns (depth - 1)


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
let terms_depth = ref 0

let generate_predicates (spec: spec) (methods : method_spec list) =
  let type_terms = Hashtbl.create 2000 in

  let term_fn = compose (fun t -> sygus_terms t (* TODO: This is here for debug. *) (default_fns @ spec.smt_fns) !terms_depth) @@ if !autogen_terms then generate_method_terms spec else (fun x -> x.terms) in

  let all_terms = List.fold_left (fun acc m -> add_terms acc (term_fn m)) type_terms methods in

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
