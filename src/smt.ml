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

type pred = (* This may not be the ideal representation *)
  | Pred of string * ty list

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
  | EForAll of ty bindlist * exp

(* Requires parsing *)
let smt_of_string : string -> exp =
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
  
  let pred : pred -> string = function
    | Pred (p, _) -> p
  
  let func : func -> string = function
    | Select _ -> "select"
    | Store _  -> "store"

  let list (f : 'a -> string) (l : 'a list) =
    l |> List.map f |> String.concat " "

  let rec binding ((Var v),e : exp binding) =
    sp "(%s %s)" v (exp e)

  and exp : exp -> string = function
    | EVar (Var v)     -> v
    | EVar (VarPost v) -> raise @@ NotImplemented "exp string of varpost"
    | EConst c         -> const c 
    | EBop (o, e1, e2) -> sp "(%s %s %s)" (bop o) (exp e1) (exp e2)
    | EUop (o, e)      -> sp "(%s %s)" (uop o) (exp e)
    | ELop (o, el)     -> sp "(%s %s)" (lop o) (list exp el)
    | ELet (bl, e)     -> sp "(let (%s) %s)" (list binding bl) (exp e)
    | EITE (g, e1, e2) -> sp "(ite %s %s %s)" (exp g) (exp e1) (exp e2)
    | EFunc (f, el)    -> sp "(%s %s)" f (list exp el)
    | EForAll _        -> raise @@ NotImplemented "exp string of forall"
end

let string_of_smt = To_String.exp
let string_of_ty = To_String.ty

type smt_query =
  { vars     : ty bindlist
  ; (* TODO: Other things? *)
  }

let string_of_smt_query = Failure "Not Implemented"
