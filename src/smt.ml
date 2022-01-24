(* Module for straightforward encoding of SMT-LIB expressions.
 * This encoding serves as the bridge between the higher-level 
 * commutativity specification, and the lower-level SAT solvers.
 *)

(* https://smtlib.cs.uiowa.edu/theories.shtml *)

open Util

type var =
  | Var of string
  | VarPost of string

type 'a binding = var * 'a
type 'a bindlist = 'a binding list

type ty =
  | TInt
  | TBool
  | TArray of ty * ty
  | TSet of ty

type const =
  | CInt of int
  | CBool of bool

type bop =
  | Sub | Mul | Mod | Div
  | Abs
  | Imp
  | Eq
  | Lt | Gt | Lte | Gte

type uop =
  | Not (* Logical negation *)
  | Neg (* Arithmetic negation *)

type lop = (* List operation *)
  | Add
  | And | Or

type pred_sig = (* This may not be the ideal representation *)
  | PredSig of string * ty list

type func =
  | Select of ty
  | Store of ty * ty

type exp =
  | EVar of var
  | EConst of const
  | EBop of bop * exp * exp
  | EUop of uop * exp
  | ELop of lop * exp list
  | ELet of exp bindlist * exp
  | EITE of exp * exp * exp
  | EFunc of string * exp list

(* Requires parsing *)
let smt_of_string (_ : string) : exp =
  raise @@ NotImplemented "smt_of_string"


module To_String = struct
  let rec ty : ty -> string = function
    | TInt  -> "Int"
    | TBool -> "Bool"
    | TArray (k,v) -> sp "(Array %s %s)" (ty k) (ty v)
    | TSet t -> sp "(Set %s)" (ty t)
  
  let const : const -> string = function
    | CInt i  -> string_of_int i
    | CBool b -> if b then "true" else "false"

  let bop : bop -> string = function
    | Sub -> "-"
    | Mul -> "*"
    | Mod -> "mod"
    | Div -> "div"
    | Imp -> "=>"
    | Eq  -> "="
    | Lt  -> "<"
    | Gt  -> ">"
    | Lte -> "<="
    | Gte -> ">="
    | Abs -> "abs"

  let uop : uop -> string = function
    | Not -> "not"
    | Neg -> "-"

  let lop : lop -> string = function
    | Add -> "+"
    | And -> "and"
    | Or  -> "or"
  
  let pred : pred_sig -> string = function
    | PredSig (p, _) -> p
  
  let func : func -> string = function
    | Select _ -> "select"
    | Store _  -> "store"

  let list (f : 'a -> string) (l : 'a list) =
    l |> List.map f |> String.concat " "

  let lop_id = function
    | Add -> "0"
    | And -> "true"
    | Or  -> "false"

  let rec binding ((Var v),e : exp binding) =
    sp "(%s %s)" v (exp e)

  and exp : exp -> string = function
    | EVar (Var v)     -> v
    | EVar (VarPost v) -> sp "%s_new" v
    | EConst c         -> const c 
    | EBop (o, e1, e2) -> sp "(%s %s %s)" (bop o) (exp e1) (exp e2)
    | EUop (o, e)      -> sp "(%s %s)" (uop o) (exp e)
    | ELop (o, [])     -> sp "(%s %s)" (lop o) (lop_id o)
    | ELop (o, el)     -> sp "(%s %s)" (lop o) (list exp el)
    | ELet (bl, e)     -> sp "(let (%s) %s)" (list binding bl) (exp e)
    | EITE (g, e1, e2) -> sp "(ite %s %s %s)" (exp g) (exp e1) (exp e2)
    | EFunc (f, el)    -> sp "(%s %s)" f (list exp el)
end

module Smt_ToMLString = struct
  let rec ty = function
    | TInt   -> "TInt"
    | TBool  -> "TBool"
    | TSet a -> sp "TSet (%s)" (ty a)
    | TArray (a,b) -> 
      "TArray " ^ ToMLString.pair ty ty (a,b)

  let var = function
    | Var v     -> "Var " ^ ToMLString.str v
    | VarPost v -> "VarPost " ^ ToMLString.str v
end

let string_of_var = function
    | Var s -> s
    | VarPost s -> s ^ "_new"
let name_of_binding ((v, ty) : ty binding) = string_of_var v
let string_of_smt = To_String.exp
let string_of_ty = To_String.ty

(* Possible don't need this
(* Remove built-in defined SMT functions? *)
let rec free_vars = function
  | EVar(Var s) -> [!s]
  | EConst(_) -> []
  | EBop(_, e1, e2) -> free_vars e1 @ free_vars e2
  | EUop(_, e) -> free_vars e
  | ELop(_, es) -> List.flatten (List.map free_vars es)
  | ELet(bindings, e) -> List.filter (fun s -> List.for_all (fun (Var s', _) -> s != !s') bindings) (free_vars e)
  | EITE(e1, e2, e3) -> free_vars e1 @ free_vars e2 @ free_vars e3
  | EFunc(fname, es) -> fname :: List.flatten (List.map free_vars es)

(* let func_of_exp fname e = "(define-func " ^ fname ^ "(" ^ List.fold_left () *)
*)


type pred = string * exp * exp

let smt_of_pred (op, e1, e2) = EFunc(op, [e1; e2])
let string_of_pred = compose string_of_smt smt_of_pred
