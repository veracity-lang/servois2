val lex : string -> Lexing.lexbuf
type 'a parser = (Lexing.lexbuf -> Smt_parser.token) -> Lexing.lexbuf -> 'a
val parse_partial : Lexing.lexbuf * string -> 'a parser -> 'a
val parse_all : 'a parser -> string -> 'a
val exp_of_string : string -> Smt.exp
val ty_of_string : string -> Smt.ty
val values_of_string : string -> (Smt.exp * Smt.exp) list
val pred_data_of_values : (Smt.exp * Smt.exp) list -> bool list
