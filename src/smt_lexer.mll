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
let float = ['+' '-']? ((digit* '.' digit+) | (digit+ '.' digit*) | digit+)

(* TODO: technically a subset of valid SMT symbols *)
let symbol = ['a'-'z' 'A'-'Z']+ ['a'-'z' 'A'-'Z' '0'-'9' '_']*

(* TODO: technically a subset of valid SMT strings *)
let str_char = ['a'-'z' 'A'-'Z' '0'-'9' '_' '-' ' ']


rule read = parse
  | wsp     { read lexbuf }
  | eof     { EOF }

  | "(" { LP }
  | ")" { RP }

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

  (* Literal integers. Used for BitVec *)
  | literalint { LITERAL (int_of_string (lexeme lexbuf)) }

  (* Float *)
  | float { FLOAT (float_of_string (lexeme lexbuf)) }

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

  (* TODO: _1 _2 *)
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
