open Util
open Smt

exception SmtParseException of string * string
exception SmtLexException of string * int

type 'a parser = (Lexing.lexbuf -> Smt_parser.token) -> Lexing.lexbuf -> 'a

let () =
  Printexc.register_printer @@
  function
  | SmtParseException (s, l) -> 
    Some (sp "SMT parse failure at %s of '%s'" l s)
  | SmtLexException (s, i) ->
    Some (sp "SMT lex failure at char %d of '%s'" i s)
  | _ -> None

let parse_partial (lexbuf, s) p = 
  try
    p Smt_lexer.read lexbuf
  with
    | Smt_parser.Error ->
      raise @@ SmtParseException (s, loc_of_parse_error lexbuf)
    | SmtLexExceptionProto i ->
      raise @@ SmtLexException (s, i)

let lex s = 
  let lexbuf = Lexing.from_string s in
  Smt_lexer.reset_lexbuf s 0 lexbuf;
  lexbuf

let parse_all p s =
  let lexbuf = lex s in
  (parse_partial (lexbuf, s) p) |>
  seq (parse_partial (lexbuf, s) Smt_parser.eof_top)

let bool_of_exp = function (* TODO *)
    | EConst(CBool t) -> t
    | _ -> failwith "bool_of_exp"

let exp_of_string = parse_all Smt_parser.exp_top
let ty_of_string = parse_all Smt_parser.ty_top
let values_of_string = parse_all Smt_parser.values_top
let pred_data_of_values = List.map (compose bool_of_exp snd)
