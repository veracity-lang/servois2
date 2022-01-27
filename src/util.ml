(*** Exceptions ***)

exception UnreachableFailure of string
exception NotImplemented of string
exception BadInputFormat of string

(*** Shorthands ***)

let sp = Printf.sprintf

(*** Utility functions ***)

let assoc_update (k : 'a) (v : 'b) (l : ('a * 'b) list) =
  (k,v) :: List.remove_assoc k l

let swap (a,b) = b,a

let flip f x y = f y x

let compose f g x = f (g x)

let null = function 
    | [] -> true
    | _ -> false

let memoize f =
    let memo = ref [] in
    fun x -> begin match List.assoc_opt x !memo with
        | Some v -> v
        | None -> let res = f x in memo := (x, res) :: !memo; res
    end

(* Randomize order of items in a list *)
let shuffle =
  let randomize = fun c -> Random.bits (), c in
  fun lst ->
    lst |>
    List.map randomize |>
    List.sort compare |>
    List.map snd

(* Get the minimum of a list, ordered by given predicate. If the minimum is not unique, gives the first such element in the list *)
let list_min p = function
    | [] -> raise @@ Failure "list_min"
    | x :: xs -> List.fold_left (fun a e -> if p e < p e then a else e) x xs

(* Sum a list of numbers *)
let list_sum = List.fold_left (fun a e -> a + e) 0

(* Reads lines from an in_channel until EOF.
 * Closes channel at the end *)
let read_all_in (chan : in_channel) : string list =
  let lines = ref [] in
  try
    while true; do
      lines := input_line chan :: !lines
    done; !lines
  with End_of_file ->
    close_in chan;
    List.rev !lines

let chars_of_string s =
  let rec f i l =
    if i < 0 then l 
    else f (i - 1) (s.[i] :: l)
  in f (String.length s - 1) []

let string_of_chars cl =
  List.map (String.make 1) cl |>
  String.concat ""

(* Reduce any more than 2 consecutive newlines to 2 newlines *)
let normalize_newlines =
  let rec f = function
  | [] -> []
  | '\n'::'\n'::'\n'::t ->
    f @@ '\n'::'\n'::t
  | '\n'::'\n'::t ->
    '\n'::'\n':: f t
  | c::t ->
    c :: f t
  in fun s ->
    chars_of_string s |>
    f |>
    string_of_chars


(* Get absolute path of a file/directory *)
let abs_path p =
  Filename.concat (Filename.dirname Sys.argv.(0)) p

(* Time the execution of a function *)
let time_exec (f : unit -> 'a) : float * 'a =
  let t0 = Unix.gettimeofday () in
  let res = f () in
  let t1 = Unix.gettimeofday () in
  t1 -. t0, res

(* Looks for an executable at provided locations,
 * returns location where it exists.
 * If not found, errors and shuts down program *)
let find_exec (name : string) (progs : string list) : string =
  match List.find_opt Sys.file_exists progs with
  | Some s -> s
  | None ->
    Printf.eprintf "%s not found at locations %s\n" name @@
      String.concat ", " progs;
    exit 1


let run_exec (prog : string) (args : string array) (output : string) =
  let chan_out, chan_in, chan_err =
    Unix.open_process_args_full prog args [||] in
  output_string chan_in output; flush chan_in; close_out chan_in;
  let _ = Unix.waitpid [] (-1) in
  let sout = read_all_in chan_out in
  let serr = read_all_in chan_err in
  sout, serr

let print_exec_result (out : string list) (err : string list) =
  Printf.printf "* * * OUT * * * \n%s\n* * * ERR * * * \n%s\n* * * * * *\n"
    (String.concat "\n" out) (String.concat "\n" err);


(*** For printing colored strings in bash ***)
module ColorPrint = struct
  type color_code =
    | Default
    | Black      | White
    | Red        | Light_red
    | Green      | Light_green
    | Yellow     | Light_yellow
    | Blue       | Light_blue
    | Magenta    | Light_magenta
    | Cyan       | Light_cyan
    | Light_gray | Dark_gray

  (* https://misc.flogisoft.com/bash/tip_colors_and_formatting *)
  let color_string (fore_color : color_code) (back_color : color_code) : string -> string =
    let foreground =
      match fore_color with
      | Default -> 39
      | Black -> 30     | White -> 97
      | Red -> 31       | Light_red -> 91
      | Green -> 32     | Light_green -> 92
      | Yellow -> 33    | Light_yellow -> 93
      | Blue -> 34      | Light_blue -> 94
      | Magenta -> 35   | Light_magenta -> 95
      | Cyan -> 36      | Light_cyan -> 96
      | Dark_gray -> 90 | Light_gray -> 37
    in
    let background =
      match back_color with
      | Default -> 49
      | Black -> 40      | White -> 107
      | Red -> 41        | Light_red -> 101
      | Green -> 42      | Light_green -> 102
      | Yellow -> 43     | Light_yellow -> 103
      | Blue -> 44       | Light_blue -> 104
      | Magenta -> 45    | Light_magenta -> 105
      | Cyan -> 46       | Light_cyan -> 106
      | Dark_gray -> 100 | Light_gray -> 47
    in
    (* \027 in decimal instead of the standard \033 in octal *)
    sp "\027[%d;%dm%s\027[0m" foreground background

end


let () =
  Printexc.register_printer @@
  function
  | UnreachableFailure s -> 
    Some (sp "UnreachableFailure (%s)" s)
  | NotImplemented s ->
    Some (sp "NotImplemented (%s)" s)
  | BadInputFormat s ->
    Some (sp "BadInputFormat (%s)" s)
  | _ -> None


module ToMLString = struct
  let list f l = sp "[%s]" @@ String.concat "; " @@ List.map f l
  let single f a = sp "(%s)" (f a)
  let pair f g (a,b) = sp "(%s, %s)" (f a) (g b)
  let triple f g h (a,b,c) = sp "(%s, %s, %s)" (f a) (g b) (h c)
  let str s = sp "\"%s\"" s
end

module Yaml_util = struct
    
  let rec string_of_value (v : Yaml.value) =
    let open Yaml in
    match v with
    | `Null -> "Null"
    | `Bool b -> sp "Bool %s" @@ string_of_bool b
    | `Float f -> sp "Float %s" @@ string_of_float f
    | `String s -> sp "String %s" s
    | `A l -> "A " ^ ToMLString.list string_of_value l
    | `O l ->
      l |>
      List.map (fun (k,v) -> sp "%s : %s" k @@ string_of_value v) |>
      String.concat " ; " |>
      sp "O { %s }"
    
  let yaml_of_file path =
    let chan = open_in path in
    let s = read_all_in chan |> String.concat "\n" in
    let y = Yaml.of_string_exn s in
    y

    
  let assoc_dict field dict msg =
    match List.assoc_opt field dict with
    | Some v -> v
    | None -> raise @@ BadInputFormat msg

  let get_dict (v : Yaml.value) msg =
    match v with
    | `O d -> d
    | _ -> raise @@ BadInputFormat msg

  let get_string (v : Yaml.value) msg =
    match v with
    | `String s -> s
    | _ -> raise @@ BadInputFormat msg

  let get_float (v : Yaml.value) msg =
    match v with
    | `Float f -> f
    | _ -> raise @@ BadInputFormat msg

  let get_list (v : Yaml.value) msg =
    match v with
    | `A l -> l
    | _ -> raise @@ BadInputFormat msg

end

let loc_of_parse_error (buf : Lexing.lexbuf) =
  let p1 = Lexing.lexeme_start_p buf in
  let p2 = Lexing.lexeme_end_p buf in
  let l1,c1 = p1.pos_lnum, p1.pos_cnum - p1.pos_bol in
  let l2,c2 = p2.pos_lnum, p2.pos_cnum - p2.pos_bol in
  Printf.sprintf "[%d.%d-%d.%d]" (l1+1) (c1+1) (l2+1) (c2+1)

(* Global options *)
let verbosity = ref true
let if_verbose action = if !verbosity then action () else ()
let print_verbose s = if_verbose (fun () -> print_string s)
let print_verbose_newline s = if_verbose (fun () -> print_string s; print_newline ())

