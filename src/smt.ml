(* Module for straightforward encoding of SMT-LIB expressions.
 * This encoding serves as the bridge between the higher-level 
 * commutativity specification, and the lower-level SAT solvers.
 *)

open Util

type var =
  | Var of string ref

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
  | Add | Sub | Mul | Mod
  | Imp
  | Eq | Neq
  | Lt | Gt | Lte | Gte

type uop =
  | Not (* Logical negation *)
  | Neg (* Arithmetic negation *)

type lop = (* List operation *)
  | And
  | Or

type pred = (* This may not be the ideal representation *)
  | Pred of string * ty list

type exp =
  | EVar of var
  | EConst of const
  | EBop of bop * exp * exp
  | EUop of uop * exp
  | ELop of lop * exp
  | EPred of pred * exp list
  | ELet of (var * exp) list * exp

(* Requires parsing *)
let smt_of_string : string -> exp =
  raise @@ NotImplemented "smt_of_string"

(* Straightforward, until we want to introduce pretty-printing *)
let string_of_smt : exp -> string =
  raise @@ NotImplemented "string_of_smt"
