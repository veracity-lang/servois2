(*** Exceptions ***)

exception UnreachableFailure of string
exception NotImplemented of string
exception BadInputFormat of string
exception Timeout

let set_timeout_handler () = Sys.set_signal Sys.sigalrm @@
  Sys.Signal_handle (fun _ -> raise Timeout)

(*** Utility functions ***)

let assoc_update (k : 'a) (v : 'b) (l : ('a * 'b) list) =
  (k,v) :: List.remove_assoc k l

let assoc_default (k : 'a) (l : ('a * 'b) list) (v : 'b) =
  match List.assoc_opt k l with
  | Some res -> res
  | _ -> v

let rec concat_unique r s = match r with
  | [] -> s
  | h :: t -> if List.mem h s then concat_unique t s else h :: concat_unique t s

let flip f x y = f y x

let swap (a,b) = b,a

let compose f g x = f (g x)

let curry f x y = f (x, y)
let uncurry f (x, y) = f x y

let curry3 f x y z = f (x, y, z)

let curry4 f x y z t = f (x, y, z, t)
let uncurry4 f (x, y, z, t) = f x y z t

let remove (x : 'a) : 'a list -> 'a list = List.filter (fun x' -> x' != x)

let first (f : 'a -> 'b) : ('a * 'c -> 'b * 'c) = fun (x, y) -> (f x, y)
let second (g : 'c -> 'd) : ('a * 'c -> 'a * 'd) = fun (x, y) -> (x, g y)

let run f = f ()

let seq a b = b (* = flip const *)

let null = function 
    | [] -> true
    | _ -> false

let fst3 = function
    | (x, _, _) -> x

let fst4 = function
    | (w, _, _, _) -> w

let memoize f =
    let memo = ref [] in
    fun x -> begin match List.assoc_opt x !memo with
        | Some v -> v
        | None -> let res = f x in memo := (x, res) :: !memo; res
    end

(* tail-recursive map: https://stackoverflow.com/a/27389842 *)
let map_tr f l =
  let rec map_aux acc = function
    | [] -> List.rev acc
    | x :: xs -> map_aux (f x :: acc) xs
  in
  map_aux [] l

(* Global options *)
let quiet = ref false
let verbosity = ref false
let very_verbose = ref false
let if_verbose action = if !verbosity || !very_verbose then action () else ()
let printf_verbose fmt = if !verbosity || !very_verbose then Printf.printf fmt else Printf.ifprintf stdout fmt
let printf_very_verbose fmt = if !very_verbose then Printf.printf fmt else Printf.ifprintf stdout fmt

(*** Shorthands ***)

let sp = Printf.sprintf
let epf = Printf.eprintf
let pfv fmt = printf_verbose fmt
let pfvv fmt = printf_very_verbose fmt
let pfnq fmt = if !quiet then Printf.ifprintf stdout fmt else Printf.printf fmt

(* Randomize order of items in a list *)
let shuffle =
  let randomize = fun c -> Random.bits (), c in
  fun lst ->
    lst |>
    List.map randomize |>
    List.sort compare |>
    List.map snd

(* Get the minimum of a list, ordered by given predicate. If the minimum is not unique, gives the first such element in the list *)
let list_min comp p = function
    | [] -> failwith "list_min"
    | x :: xs -> fst @@ List.fold_left (fun (a, cached_val) e -> let e_val = p e in if comp e_val cached_val then (e, e_val) else (a, cached_val)) (x, p x) xs

let int_comp x y = x < y
let lex_comp (x1, y1) (x2, y2) = x1 < x2 || x1 = x2 && y1 < y2

(* Sum a list of numbers *)
let list_sum = List.fold_left ( + ) 0

let iter_prod f l1 l2 = List.iter (fun e1 -> List.iter (fun e2 -> f e1 e2) l2) l1

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

let unlines ?(trailing_newline = true) = if trailing_newline
    then List.fold_left (fun acc e -> acc ^ e ^ "\n") ""
    else String.concat "\n"

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
    Printf.eprintf "error: %s not found at locations %s\n" name @@
      String.concat ", " progs;
    exit 1

let waitpid_poll ?(interval=0.01) pid = 
  let ret = ref 0 in
  while (!ret = 0) do
    ret := fst @@ Unix.waitpid [Unix.WNOHANG] pid;
    if !ret = 0 then Unix.sleepf interval
  done

let output_string_long buf str =
  let i = ref 0 in
  let len = String.length str in
  let size = 16384 in
  while !i < len do
    let sublen = min size (len - i)
    output_string buf (String.sub str !i sublen);
    flush buf;
    i := !i + size
  done

let run_exec (prog : string) (args : string array) (output : string) =
  let chan_out, chan_in, chan_err =
    Unix.open_process_args_full prog args [||] in
  let pid = Unix.process_full_pid (chan_out, chan_in, chan_err) in
  Sys.set_signal Sys.sigalrm (
      Sys.Signal_handle (fun _ ->
          Unix.kill pid Sys.sigkill;
          raise Timeout)
      );
  output_string_long chan_in output; close_out chan_in;
  let _ = waitpid_poll pid in
  set_timeout_handler ();
  let sout = read_all_in chan_out in
  let serr = read_all_in chan_err in
  sout, serr

let print_exec_result (out : string list) (err : string list) =
  pfv "* * * OUT * * * \n%s\n* * * ERR * * * \n%s\n* * * * * *\n"
    (String.concat "\n" out) (String.concat "\n" err)


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
  let option f = function
    | Some s -> sp "Some %s" (f s)
    | None -> "None"
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

(* 
   Pre-emptive runtime bound on a function, modified from:
   https://discuss.ocaml.org/t/todays-trick-memory-limits-with-gc-alarms/4431/2
*)

let run_with_time_limit (limit : float) f =
  set_timeout_handler ();
  let _ = Unix.setitimer Unix.ITIMER_REAL Unix.{it_value = limit; it_interval = 0. } in
  Fun.protect f ~finally:(fun () ->
    ignore @@ Unix.setitimer Unix.ITIMER_REAL Unix.{it_value = 0.; it_interval = 0. }
  )

let remove_duplicate lst =
  let rec is_member n mlst =
    match mlst with
    | [] -> false
    | h::tl ->
        begin
          if h=n then true
          else is_member n tl
        end
  in
  let rec loop lbuf =
    match lbuf with
    | [] -> []
    | h::tl ->
        begin
        let rbuf = loop tl
        in
          if is_member h rbuf then rbuf
          else h::rbuf
        end
  in
  loop lst
