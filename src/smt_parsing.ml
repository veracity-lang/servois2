open Util
open Smt


exception SmtParseException of string * string
exception SmtLexException of string * int

let () =
  Printexc.register_printer @@
  function
  | SmtParseException (s, l) -> 
    Some (sp "SMT parse failure at %s of '%s'" l s)
  | SmtLexException (s, i) ->
    Some (sp "SMT lex failure at char %d of '%s'" i s)
  | _ -> None

let parse p (s : string) =
  let lexbuf = Lexing.from_string s in
  Smt_lexer.reset_lexbuf s 0 lexbuf;
  try
    p Smt_lexer.read lexbuf
  with
    | Smt_parser.Error ->
      raise @@ SmtParseException (s, loc_of_parse_error lexbuf)
    | SmtLexExceptionProto i ->
      raise @@ SmtLexException (s, i)

let bool_of_exp = function (* TODO *)
    | EConst(CBool t) -> t
    | _ -> failwith "bool_of_exp"

let exp_of_string = parse Smt_parser.exp_top
let ty_of_string = parse Smt_parser.ty_top
let values_of_string = parse Smt_parser.values_top
let parse_pred_data s = (match s with "" -> [] | s -> List.map (compose bool_of_exp snd) @@ values_of_string s)
