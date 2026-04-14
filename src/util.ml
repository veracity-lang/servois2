(*** Exceptions ***)

exception UnreachableFailure of string
exception NotImplemented of string
exception BadInputFormat of string
exception Timeout

let set_timeout_handler () = Sys.set_signal Sys.sigalrm @@
  Sys.Signal_handle (fun _ -> raise Timeout)

(*** Utility functions ***)


let write_temp_string (s : string) : string =
  let filename = Filename.temp_file "prefix_" ".smt" in
  let oc = open_out filename in
  output_string oc s;
  close_out oc;
  filename

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
let diagram = ref false
let dump_queries = ref false
let query_counter = ref 0
let examine_script_text = {|#!/usr/bin/perl
use strict;
use warnings;

# Convert all .dot diagram files to .jpg
for my $dot (sort glob("servois2_diagram_*.dot")) {
    (my $jpg = $dot) =~ s/\.dot$/.jpg/;
    print "Converting $dot -> $jpg\n";
    system("dot", "-Tjpg", "-o", $jpg, $dot) == 0
        or warn "dot failed for $dot: $?\n";
}

# Parse run info from servois2_run_info.txt
my ($cmdline, $method1, $method2, $mode_label, $yaml) = ('', '?', '?', 'Commute', '');
if (open(my $inf, '<', 'servois2_run_info.txt')) {
    $cmdline = <$inf> // '';
    chomp $cmdline;
    close($inf);

    my @args = split(/\s+/, $cmdline);

    # Determine mode
    if    (grep { $_ eq '--leftmover'  } @args) { $mode_label = 'Left Mover';  }
    elsif (grep { $_ eq '--rightmover' } @args) { $mode_label = 'Right Mover'; }
    else                                         { $mode_label = 'Commute';     }

    # AE qualifier
    # if (grep { $_ eq '-ae' || $_ eq '--forall-exists' } @args) {
    #    $mode_label .= ' (AE \x{2200}\x{2203})';
    # }

    # Extract positional args (skip flags and their values)
    my @pos;
    my %takes_val = map { $_ => 1 } qw(
        -o --prover --timeout --lattice-timeout --terms-depth --mc-term
    );
    my $skip_next = 0;
    for my $a (@args) {
        if ($skip_next)          { $skip_next = 0; next; }
        if ($takes_val{$a})      { $skip_next = 1; next; }
        next if $a =~ /^-/;
        push @pos, $a;
    }
    # pos: [exe, subcommand, yaml, m1, m2, ...]
    $yaml    = $pos[2] // '';
    $method1 = $pos[3] // '?';
    $method2 = $pos[4] // '?';
}

# Escape for HTML
sub he {
    my $s = shift;
    $s =~ s/&/&amp;/g; $s =~ s/</&lt;/g; $s =~ s/>/&gt;/g;
    return $s;
}

# Generate HTML viewer
my $html_file = "servois2_examine.html";
open(my $out, '>', $html_file) or die "Cannot write $html_file: $!";

my $title = "$method1 \x{2016} $method2";  # ‖

print $out <<HEADER;
<!DOCTYPE html>
<html>
<head>
<meta charset="utf-8">
<title>Servois2: $title</title>
<style>
  body    { font-family: monospace; background: #1e1e1e; color: #ccc;
            margin: 0; padding: 20px; }
  h1      { color: #9cdcfe; margin-bottom: 0.2em; }
  .banner { margin: 0.4em 0 1.2em 0; }
  .mode   { font-size: 1.4em; font-weight: bold; color: #f9c74f; }
  .methods { font-size: 1.6em; font-weight: bold; color: #90e0ef; }
  .cmdline { font-size: 1.0em; color: #888; margin-top: 0.4em; }
  h2      { color: #4ec9b0; margin-top: 2em; border-top: 1px solid #444;
            padding-top: 0.5em; }
  .row    { display: flex; gap: 20px; align-items: flex-start;
            margin: 10px 0 30px 0; flex-wrap: wrap; }
  .query  { background: #252526; border: 1px solid #444; padding: 10px;
            white-space: pre; overflow-x: auto; flex: 1; min-width: 400px;
            font-size: 12px; line-height: 1.4; }
  .diagram img { border: 1px solid #555; max-width: 700px; height: auto; }
  .result     { display: inline-block; margin-left: 0.6em; padding: 2px 10px;
                border-radius: 4px; font-weight: bold; font-size: 0.85em; }
  .sat        { background: #5a1a1a; color: #f28b82; }
  .unsat      { background: #1a3a1a; color: #81c995; }
  .unknown    { background: #2a2a1a; color: #f9c74f; }
  .phi-box    { margin: 1em 0 1.6em 0; padding: 12px 16px;
                background: #252526; border: 1px solid #555;
                border-radius: 4px; font-size: 1em; line-height: 1.8; }
  .phi-label  { color: #888; font-size: 1.4em; margin-right: 0.5em; }
  .phi-val    { color: #ce9178; font-weight: bold; font-size: 1.4em; white-space: pre-wrap; }
  .toc        { margin: 1.2em 0 2em 0; padding: 10px 16px;
                background: #252526; border: 1px solid #444;
                border-radius: 4px; display: inline-block; min-width: 200px; }
  .toc strong { color: #9cdcfe; }
  .toc ul     { margin: 0.4em 0 0 0; padding-left: 1.2em; }
  .toc li     { margin: 0.2em 0; }
  .toc a      { color: #4ec9b0; text-decoration: none; }
  .toc a:hover { text-decoration: underline; }
</style>
</head>
<body>
<h1>Servois2 Output</h1>
<div class="banner">
  <div class="methods">Query: <span class="mode">$method1 ($mode_label) $method2</span></div>
  <div class="cmdline">@{[he($cmdline)]}</div>
</div>
HEADER

# Show final phi / phi-tilde if available
for my $entry (
    [ 'servois2_phi.txt',      "\x{03c6}",        'commutativity condition'     ],
    [ 'servois2_phitilde.txt', "\x{03c6}\x{0303}", 'non-commutativity condition' ],
) {
    my ($file, $sym, $label) = @$entry;
    next unless -f $file;
    open(my $fh, '<', $file) or next;
    my $val = do { local $/; <$fh> }; close($fh); chomp $val;
    print $out "<div class='phi-box'>"
             . "<span class='phi-label'>$sym &nbsp;($label):</span>"
             . "<span class='phi-val'>" . he($val) . "</span>"
             . "</div>\n";
}

# Read query indices from the manifest (only queries from this run)
my @indices;
if (open(my $mfh, '<', 'servois2_run_manifest.txt')) {
    while (my $line = <$mfh>) { chomp $line; push @indices, $line if $line =~ /^\d+$/; }
    close($mfh);
}

if (!@indices) {
    print $out "<p>No queries recorded for this run.</p>\n";
} else {
    # Table of contents
    print $out "<nav class='toc'><strong>Queries</strong><ul>\n";
    for my $padded (@indices) {
        my $result = '';
        my $rfile = "servois2_result_${padded}.txt";
        if (open(my $rfh, '<', $rfile)) { $result = <$rfh>; chomp $result; close($rfh); }
        my $badge = $result ? " <span class='result $result'>$result</span>" : '';
        print $out "<li><a href='#query-$padded'>Query $padded</a>$badge</li>\n";
    }
    print $out "</ul></nav>\n";

    # Per-query sections
    for my $padded (@indices) {
        my $qfile    = "servois2_query_${padded}.smt";
        my $dfile_jpg = "servois2_diagram_${padded}.jpg";

        open(my $qfh, '<', $qfile) or die "Cannot open $qfile: $!";
        my $text = do { local $/; <$qfh> };
        close($qfh);
        $text = he($text);

        my $result = '';
        my $rfile = "servois2_result_${padded}.txt";
        if (open(my $rfh, '<', $rfile)) { $result = <$rfh>; chomp $result; close($rfh); }
        my $badge = $result ? "<span class='result $result'>$result</span>" : '';
        print $out "<h2 id='query-$padded'>Query $padded $badge</h2>\n<div class='row'>\n";
        print $out "<div class='query'>$text</div>\n";
        if (-f $dfile_jpg) {
            print $out "<div class='diagram'><img src='$dfile_jpg' alt='Diagram $padded'></div>\n";
        }
        print $out "</div>\n";
    }
}

print $out "</body>\n</html>\n";
close($out);
print "Wrote $html_file\n";
|}

let write_examine_script () =
    (* Write examine.pl *)
    let oc = open_out "examine.pl" in
    output_string oc examine_script_text;
    close_out oc;
    Unix.chmod "examine.pl" 0o755;
    (* Write run info: full argv on one line *)
    let oc = open_out "servois2_run_info.txt" in
    output_string oc (String.concat " " (Array.to_list Sys.argv));
    output_char oc '\n';
    close_out oc;
    (* Reset manifest for this run *)
    let oc = open_out "servois2_run_manifest.txt" in
    close_out oc

let dump_query_if_enabled (s : string) : unit =
    if !dump_queries then begin
        let idx = !query_counter in
        query_counter := idx + 1;
        if idx = 0 then write_examine_script ();
        let filename = Printf.sprintf "servois2_query_%04d.smt" idx in
        let oc = open_out filename in
        output_string oc s;
        output_char oc '\n';
        close_out oc;
        (* Append this index to the run manifest *)
        let oc = open_out_gen [Open_append; Open_creat] 0o644 "servois2_run_manifest.txt" in
        output_string oc (Printf.sprintf "%04d\n" idx);
        close_out oc
    end

(* Call this after each solver call to record sat/unsat/unknown alongside the query. *)
let dump_result_if_enabled (result : string) : unit =
    if !dump_queries && !query_counter > 0 then begin
        let idx = !query_counter - 1 in
        let filename = Printf.sprintf "servois2_result_%04d.txt" idx in
        let oc = open_out filename in
        output_string oc result;
        output_char oc '\n';
        close_out oc
    end

(* Call after synthesis to record the final phi and phi-tilde. *)
let dump_phi_if_enabled (phi : string) (phi_tilde : string) : unit =
    if !dump_queries then begin
        let write name s =
            let oc = open_out name in
            output_string oc s;
            output_char oc '\n';
            close_out oc
        in
        write "servois2_phi.txt" phi;
        write "servois2_phitilde.txt" phi_tilde
    end

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

let run_exec (prog : string) (args : string array) (output : string) =
  if String.length output > 16384 then
    (* We write to a temporary file and use that. *)
    let tmp_out = open_out "_servois2_temp.smt" in
    output_string tmp_out output;
    flush tmp_out;
    close_out tmp_out;
    let chan_out, chan_in, chan_err =
      Unix.open_process_args_full prog (Array.append args [|"_servois2_temp.smt"|]) [||] in
    let pid = Unix.process_full_pid (chan_out, chan_in, chan_err) in
    Sys.set_signal Sys.sigalrm (
        Sys.Signal_handle (fun _ ->
            Unix.kill pid Sys.sigkill;
            raise Timeout)
        );
    let _ = waitpid_poll pid in
    Sys.remove "_servois2_temp.smt";
    let sout = read_all_in chan_out in
    let serr = read_all_in chan_err in
    sout, serr
  else   
    let chan_out, chan_in, chan_err =
      Unix.open_process_args_full prog args [||] in
    let pid = Unix.process_full_pid (chan_out, chan_in, chan_err) in
    Sys.set_signal Sys.sigalrm (
        Sys.Signal_handle (fun _ ->
            Unix.kill pid Sys.sigkill;
            raise Timeout)
        );
    output_string chan_in output; close_out chan_in;
    let _ = waitpid_poll pid in
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
