open Spec
open Smt

(* let f l1 l2 = 
   let res = List.fold_left (fun acc x ->
     List.fold_left (fun acc y -> (x * y) :: acc) acc l2
   ) [] l1 in
   List.rev res *)

let string_of_binop = function
  | Mul    -> "*"
  | Div    -> "/"
  | Sub    -> "-"
  | Lt     -> "<"
  | Lte    -> "<="
  | Gt     -> ">"
  | Gte    -> ">="
  | Eq     -> "=="

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
  (* | EBop of bop * exp * exp
  | EUop of uop * exp
  | ELop of lop * exp list
  | ELet of exp bindlist * exp
  | EITE of exp * exp * exp
  | EFunc of string * exp list
  | EForAll of ty bindlist * exp *)

let add_terms (type_terms) (tl: term_list list) =
  List.iter (fun (ty, el) -> 
    match Hashtbl.find_opt type_terms ty with 
    | Some t -> Hashtbl.replace type_terms ty (el @ t)
    | None -> Hashtbl.add type_terms ty el
  ) tl;
  type_terms

let generate_predicates (spec: spec) (method1: method_spec) (method2: method_spec) : pred list =
  Printf.printf "here\n";
  let type_terms = Hashtbl.create 100 in

  let all_terms = add_terms (add_terms type_terms method1.terms) method2.terms in

  let pred_list = ref [] in
  List.iter (fun (PredSig (name,[ty1;ty2])) ->
    List.iter (
      fun left ->
      List.iter (
        fun right -> 
         pred_list := (name,left,right) :: !pred_list
      ) (Hashtbl.find all_terms ty2)
    ) (Hashtbl.find all_terms ty1)
  ) spec.preds;
  (* List.iter (fun (name,left,right) -> Printf.printf "-> Preds: %s, %s, %s\n" name (string_of_exp left) (string_of_exp right) ) !pred_list; *)

  !pred_list

