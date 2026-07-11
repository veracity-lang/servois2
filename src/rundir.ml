(* Run-directory allocation, shared by servois2, veracity, and conquoer.

   Each tool is both a standalone CLI (which must root its own output tree) and
   a library called by the layer above (which must write inside the caller's
   tree).  Both cases are served by resolving the run directory in this order:

     1. a directory supplied by the calling layer (Rundir.set_root)
     2. an explicit --out-dir flag (which also calls set_root)
     3. the tool's environment variable, e.g. $SERVOIS2_OUT
     4. default: ./<tool>_output/run_NNNN/ in the CWD

   Standalone, a tool falls through to (4) and becomes the root of the tree.
   Called as a library it takes (1) and nests underneath its caller.  The
   environment variable exists so the hand-down survives an exec boundary. *)

(* Each tool owns its own root cell (all three link into one process, so a
   single shared global would have them clobbering each other).  A tool's cell
   holds the directory supplied by its caller, if any. *)

let rec mkdir_p d =
  if d <> "" && d <> "." && d <> "/" && not (Sys.file_exists d) then begin
    mkdir_p (Filename.dirname d);
    try Unix.mkdir d 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ()
  end

(* Claim the next free run_NNNN under [base].  mkdir is atomic on POSIX, so a
   losing racer sees EEXIST and advances; benchmark sweeps run these in
   parallel. *)
let next_run_dir base =
  mkdir_p base;
  let rec claim n =
    if n > 9999 then failwith (base ^ ": no free run_NNNN slot")
    else
      let d = Filename.concat base (Printf.sprintf "run_%04d" n) in
      match Unix.mkdir d 0o755 with
      | () -> d
      | exception Unix.Unix_error (Unix.EEXIST, _, _) -> claim (n + 1)
  in
  claim 1

(* base/latest -> run_NNNN, so you can always open the same path while
   iterating.  Best-effort: a filesystem without symlinks just skips it. *)
let update_latest base run =
  let link = Filename.concat base "latest" in
  try
    (try Unix.unlink link with Unix.Unix_error (Unix.ENOENT, _, _) -> ());
    Unix.symlink (Filename.basename run) link
  with _ -> ()

(* Resolve a tool's run directory, creating it if needed.  [root] is that
   tool's own cell: if the caller already handed a directory down, that wins.
   Idempotent -- the result is memoized back into [root], so every later call
   returns the same dir, and a parent can reset the cell to None to detach. *)
let resolve ~root ~tool ~env_var =
  match !root with
  | Some d -> mkdir_p d; d
  | None ->
    let d =
      match Sys.getenv_opt env_var with
      | Some d when d <> "" -> mkdir_p d; d
      | _ ->
        let base = tool ^ "_output" in
        let run = next_run_dir base in
        update_latest base run;
        run
    in
    root := Some d;
    d

(* Allocate a subdirectory of [parent] for a child tool or a numbered unit of
   work.  This is how a parent hands a directory down. *)
let child ~parent ~name =
  let d = Filename.concat parent name in
  mkdir_p d;
  d

let file ~dir name = Filename.concat dir name

(* ---- manifest.json -------------------------------------------------------

   One schema at every level of the tree, so a single script can walk it from
   any node.  Children are recorded by relative path, which keeps the whole
   tree movable (and tar-able for an artifact). *)

let json_escape s =
  let b = Buffer.create (String.length s + 8) in
  String.iter
    (fun c ->
      match c with
      | '"' -> Buffer.add_string b "\\\""
      | '\\' -> Buffer.add_string b "\\\\"
      | '\n' -> Buffer.add_string b "\\n"
      | '\r' -> Buffer.add_string b "\\r"
      | '\t' -> Buffer.add_string b "\\t"
      | c when Char.code c < 0x20 ->
        Buffer.add_string b (Printf.sprintf "\\u%04x" (Char.code c))
      | c -> Buffer.add_char b c)
    s;
  Buffer.contents b

let json_string s = "\"" ^ json_escape s ^ "\""
let json_list f xs = "[" ^ String.concat "," (List.map f xs) ^ "]"

type artifact = { kind : string; path : string }
type child_ref = { child_tool : string; child_path : string }

(* [result] is the tool's verdict, [artifacts] the files it wrote (relative to
   [dir]), [children] the nested run dirs it handed out. *)
let write_manifest ~dir ~tool ~input ~result ?(artifacts = []) ?(children = [])
    () =
  let oc = open_out (file ~dir "manifest.json") in
  let field k v = Printf.sprintf "  %s: %s" (json_string k) v in
  let artifact a =
    Printf.sprintf "{%s: %s, %s: %s}" (json_string "kind")
      (json_string a.kind) (json_string "path") (json_string a.path)
  in
  let child c =
    Printf.sprintf "{%s: %s, %s: %s}" (json_string "tool")
      (json_string c.child_tool) (json_string "path")
      (json_string c.child_path)
  in
  let body =
    [ field "tool" (json_string tool);
      field "input" (json_string input);
      field "args" (json_list json_string (Array.to_list Sys.argv));
      field "result" (json_string result);
      field "artifacts" (json_list artifact artifacts);
      field "children" (json_list child children) ]
  in
  output_string oc "{\n";
  output_string oc (String.concat ",\n" body);
  output_string oc "\n}\n";
  close_out oc
