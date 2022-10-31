(* Module for straightforward encoding of SMT-LIB expressions.
 * This encoding serves as the bridge between the higher-level 
 * commutativity specification, and the lower-level SAT solvers.
 *)

(* https://smtlib.cs.uiowa.edu/theories.shtml *)

open Util

exception SmtLexExceptionProto of int

type var =
  | Var of string
  | VarPost of string
  | VarM of bool * string (* bool represents whether it is the first/left method *)

type 'a binding = var * 'a
type 'a bindlist = 'a binding list

type ty =
  | TInt
  | TBool
  | TString
  | TArray of ty * ty
  | TSet of ty
  | TBitVector of int 
  | TGeneric of string

type const =
  | CInt of int
  | CBool of bool
  | CString of string

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

type bindop =
  | Let
  | Exists
  | Forall

type exp =
  | EVar of var
  | EArg of int
  | EConst of const
  | EBop of bop * exp * exp
  | EUop of uop * exp
  | ELop of lop * exp list
  (* TODO: Make the following two cases just this: | EBinding of bindop * exp bindlist * exp *)
  | ELet of exp bindlist * exp
  | EForall of ty bindlist * exp
  | EExists of ty bindlist * exp
  | EITE of exp * exp * exp
  | EFunc of string * exp list

let rec make_recursive (f : exp -> exp) (* f only needs to work on EVar, EArg, EConst *) = function
  | EVar v -> f (EVar v)
  | EArg i -> f (EArg i)
  | EConst c -> f (EConst c)
  | EBop(b, el, er) -> EBop(b, make_recursive f el, make_recursive f er)
  | EUop(u, e) -> EUop(u, make_recursive f e)
  | ELop(lop, es) -> ELop(lop, List.map (make_recursive f) es)
  | ELet(binds, e) -> ELet(binds, make_recursive f e)
  | EForall(binds, e) -> EForall(binds, make_recursive f e)
  | EExists(binds, e) -> EExists(binds, make_recursive f e)
  | EITE(i, t, e) -> EITE(make_recursive f i, make_recursive f t, make_recursive f e)
  | EFunc(s, es) -> EFunc(s, List.map (make_recursive f) es)


let name_arguments (f : int -> string) = make_recursive (function | EArg i -> EVar (Var (f i)) | x -> x)

module To_String = struct
  let var : var -> string = function
    | Var s     -> s
    | VarPost s -> s ^ "_new"
    | VarM (b, s)     -> sp "m%d_%s" (if b then 1 else 2) s

  let rec ty : ty -> string = function
    | TInt  -> "Int"
    | TBool -> "Bool"
    | TString -> "String"
    | TArray (k,v) -> sp "(Array %s %s)" (ty k) (ty v)
    | TSet t -> sp "(Set %s)" (ty t)
    | TBitVector w -> sp "(_ BitVec %d)" w
    | TGeneric g -> g
  
  let ty_binding : ty binding -> string = function
    | (v, t) -> sp "(%s %s)" (var v) (ty t)
  
  let const : const -> string = function
    | CInt i  -> string_of_int i
    | CBool b -> if b then "true" else "false"
    | CString s -> sp "\"%s\"" s

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

  let rec exp_binding (v, e : exp binding) =
    sp "(%s %s)" (var v) (exp e)

  and exp : exp -> string = function
    | EVar v           -> var v
    | EArg n           -> sp "$%d" n
    | EConst c         -> const c 
    | EBop (o, e1, e2) -> sp "(%s %s %s)" (bop o) (exp e1) (exp e2)
    | EUop (o, e)      -> sp "(%s %s)" (uop o) (exp e)
    | ELop (o, [])     -> sp "(%s %s)" (lop o) (lop_id o)
    | ELop (o, el)     -> sp "(%s %s)" (lop o) (list exp el)
    | ELet (bl, e)     -> sp "(let (%s) %s)" (list exp_binding bl) (exp e)
    | EForall (bl, e)     -> sp "(forall (%s) %s)" (list ty_binding bl) (exp e)
    | EExists (bl, e)     -> sp "(exists (%s) %s)" (list ty_binding bl) (exp e)
    | EITE (g, e1, e2) -> sp "(ite %s %s %s)" (exp g) (exp e1) (exp e2)
    | EFunc (f, el)    -> sp "(%s %s)" f (list exp el)
end

module Smt_ToMLString = struct
  let rec ty = function
    | TInt   -> "TInt"
    | TBool  -> "TBool"
    | TString -> "TString"
    | TSet a -> "TSet " ^ ToMLString.single ty a
    | TBitVector w -> "TBitVector " ^ (string_of_int w)
    | TArray (a,b) -> 
      "TArray " ^ ToMLString.pair ty ty (a,b)
    | TGeneric g -> "TGeneric " ^ ToMLString.str g

  let var = function
    | Var v     -> "Var " ^ ToMLString.str v
    | VarPost v -> "VarPost " ^ ToMLString.str v
    | VarM (b, s) -> "VarM " ^ ToMLString.pair (fun b -> if b then "1" else "2") ToMLString.str (b, s)

  let ty_bindlist = ToMLString.list (ToMLString.pair var ty)

  let const = function
    | CInt i  -> "CInt " ^ string_of_int i
    | CBool b -> if b then "CBool true" else "CBool false"
    | CString s -> "CString " ^ ToMLString.str s

  let bop = function
    | Sub -> "Sub"
    | Mul -> "Mul"
    | Mod -> "Mod"
    | Div -> "Div"
    | Imp -> "Imp"
    | Eq  -> "Eq"
    | Lt  -> "Lt"
    | Gt  -> "Gt"
    | Lte -> "Lte"
    | Gte -> "Gte"
    | Abs -> "Abs"

  let uop = function
    | Not -> "Not"
    | Neg -> "Neg"

  let lop = function
    | Add -> "Add"
    | And -> "And"
    | Or  -> "Or"

  let rec exp = function
    | EVar v   -> "EVar " ^ ToMLString.single var v
    | EArg n   -> "EArg " ^ string_of_int n
    | EConst c -> "EConst " ^ ToMLString.single const c
    | EBop (o, e1, e2) -> "EBop " ^ ToMLString.triple bop exp exp (o,e1,e2)
    | EUop (o, e)      -> "EUop " ^ ToMLString.pair uop exp (o,e)
    | ELop (o, el)     -> "ELop " ^ ToMLString.pair lop (ToMLString.list exp) (o,el)
    | ELet (bl, e)     -> "ELet " ^
      ToMLString.pair (ToMLString.list (ToMLString.pair var exp)) exp (bl,e)
    | EForall (bl, e)     -> "EForall " ^
      ToMLString.pair (ToMLString.list (ToMLString.pair var ty)) exp (bl,e)
    | EExists (bl, e)     -> "EExists " ^
      ToMLString.pair (ToMLString.list (ToMLString.pair var ty)) exp (bl,e)
    | EITE (g, e1, e2) -> "EITE " ^ ToMLString.triple exp exp exp (g,e1,e2)
    | EFunc (f, el)    -> "EFunc " ^
      ToMLString.pair ToMLString.str (ToMLString.list exp) (f,el)
end

let string_of_var = To_String.var
let name_of_binding : ty binding -> string = compose string_of_var fst
let string_of_smt = To_String.exp
let string_of_ty = To_String.ty
let string_of_ty_binding = To_String.ty_binding

let make_new : ty binding -> ty binding = function
    | Var s, ty    -> VarPost s, ty
    | VarM _, _    -> raise @@ Failure "Cannot 'new' a method variable."
    | VarPost _, _ -> raise @@ Failure "Cannot 'new' a post variable."

let make_new_bindings = List.map make_new

type pred = string * exp * exp

let smt_of_pred (op, e1, e2) = EFunc(op, [e1; e2])
let string_of_pred = compose string_of_smt smt_of_pred
