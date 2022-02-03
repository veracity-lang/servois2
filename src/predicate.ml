open Spec
open Smt


let string_of_binop = function
  | Mul    -> "*"
  | Div    -> "/" (* TODO: I think smtlib2 actually uses "div"? *)
  | Sub    -> "-"
  | Lt     -> "<"
  | Lte    -> "<="
  | Gt     -> ">"
  | Gte    -> ">="
  | Eq     -> "=="
  | Mod    -> "mod"
  | Abs    -> "abs"
  | Imp    -> "=>"

let string_of_lop = function
  | Add -> "+"
  | And -> "&&"
  | Or -> "||"

let rec string_of_exp (e: exp) =
  match e with
  | EVar (Var str) -> str
  | EVar (VarPost str) -> str 
  | EConst (CInt i) -> Int.to_string i
  | EConst (CBool b) -> Bool.to_string b
  | EBop (bop,exp1,exp2) -> "(" ^ string_of_binop bop ^ " "^ string_of_exp exp1 ^ " "^ string_of_exp exp2 ^ ")" 
  | ELop (lop, [exp1; exp2]) ->  "(" ^ string_of_lop lop ^ " "^ string_of_exp exp1 ^ " "^ string_of_exp exp2 ^ ")" 
  | _ -> "other exp"


let is_reflx (op: string) (exp1: exp) (exp2: exp) : bool =
  match op with
  | "=" -> 
    if String.equal (string_of_exp exp1) (string_of_exp exp2) then
      true
    else 
      false
  | _ -> false


let is_symm (op: string) (exp1: exp) (exp2: exp) =
  function preds_list ->
  match op with
  | "=" -> 
    List.exists (fun (o,e1,e2) -> 
        (String.equal o op) && (String.equal (string_of_exp exp1) (string_of_exp e2)) 
        && (String.equal (string_of_exp exp2) (string_of_exp e1))
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
  (* List.iter (fun p -> Printf.printf "-> Preds: %s\n" (string_of_pred p)) !pred_list; *)

  !pred_list

