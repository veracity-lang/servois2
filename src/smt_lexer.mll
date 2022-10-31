{
  open Lexing
  open Smt_parser
  exception Error of string

  let reset_lexbuf (filename:string) (lnum:int) lexbuf : unit =
    lexbuf.lex_curr_p <- {
      pos_fname = filename;
      pos_cnum = 0;
      pos_bol = 0;
      pos_lnum = lnum;
    }
}

let wsp = [' ' '\t' '\n']+
let digit = ['0'-'9']
let literalint = digit+

(* TODO: technically a subset of valid SMT symbols *)
let symbol = ['a'-'z' 'A'-'Z']+ ['a'-'z' 'A'-'Z' '0'-'9' '_' '.']*

(* TODO: technically a subset of valid SMT strings *)
let str_char = ['a'-'z' 'A'-'Z' '0'-'9' '_' '-' ' ']


rule read = parse
  | wsp     { read lexbuf }
  | eof     { EOF }

  | "(" { LP }
  | ")" { RP }
  | "_" { UNDERSCORE }

  (* Type *)
  | "Int"    { INT }
  | "Bool"   { BOOL }
  | "Array"  { ARRAY }
  | "Set"    { SET }
  | "String" { STRING }
  | "BitVec" { BITVEC }

  (* Bool *)
  | "true"  { TRUE }
  | "false" { FALSE }

  (* Integer literals *)
  | literalint { LITERAL (int_of_string (lexeme lexbuf)) }

  (* Arguments *)
  | "$" digit* { 
    let s = lexeme lexbuf in
    let s' = String.sub s 1 (String.length s - 1) in
    let n = int_of_string s' in
    ARG n
  }


  (* Bop *)
  | "-"   { SUB }
  | "*"   { MUL }
  | "mod" { MOD }
  | "div" { DIV }
  | "=>"  { IMP }
  | "="   { EQ }
  | "<"   { LT }
  | ">"   { GT }
  | "<="  { LTE }
  | ">="  { GTE }
  | "abs" { ABS }
  | "forall" { FORALL }
  | "exists" { EXISTS }

  (* Uop *)
  | "not" { NOT }
  (* NEG is same as SUB *)

  (* Lop *)
  | "+"   { ADD }
  | "and" { AND }
  | "or"  { OR }

  | "let" { LET }
  | "ite" { ITE }

  | '\"' str_char* '\"' {
    let s = lexeme lexbuf in
    let s' = String.sub s 1 (String.length s - 2)
    in STR s'
  }

  | "m1_" symbol {
    let s = lexeme lexbuf in
    let s' = String.sub s 3 (String.length s - 3)
    in SYMBOL_M1 s'
  }
  | "m2_" symbol {
    let s = lexeme lexbuf in
    let s' = String.sub s 3 (String.length s - 3)
    in SYMBOL_M2 s'
  }

  | symbol "_new" {
    let s = lexeme lexbuf in
    let s' = String.sub s 0 (String.length s - 4)
    in SYMBOL_NEW s'
  }

  | symbol "_1" {
    let s = lexeme lexbuf in
    let s' = String.sub s 0 (String.length s - 2)
    in SYMBOL s'
  }

  | symbol "_2" {
    let s = lexeme lexbuf in
    let s' = String.sub s 0 (String.length s - 2)
    in SYMBOL_NEW s'
  }

  (* Variable or function *)
  | symbol  { SYMBOL (lexeme lexbuf) }
  
  | _ { raise (Smt.SmtLexExceptionProto (lexeme_start lexbuf)) }
