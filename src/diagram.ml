(* Graphviz dot diagram generation for commutativity queries.
 *
 * Produces one .dot file per query showing the state diamond:
 *
 *   init --> s1 --(m2)--> s12
 *    |                      |
 *   (m2)               states_equal?
 *    |                      |
 *   s2 --(m1)--> s21 ------+
 *
 * When the query is SAT, state variable values from the model are shown
 * inside each node.  For AE queries, only the free-variable states
 * (init, s1, s12) carry model values; s2 and s21 show names only.
 *)

open Util
open Smt
open Spec

let diagram_counter = ref 0

(* Build EVar expressions for all state variables at the given suffixes,
 * in the order (suffixes × state bindings).  This is the order in which
 * they are appended to get_vals so that the model response can be
 * positionally matched back. *)
let state_var_exps (state : ty bindlist) (suffixes : string list) : exp list =
    List.concat_map (fun sfx ->
        List.map (fun db -> EVar (Var (name_of_binding db ^ sfx))) state
    ) suffixes

(* Strip the "m1_" / "m2_" mangling prefix added by mangle_method_vars. *)
let display_name s =
    if String.length s > 3 &&
       (String.sub s 0 3 = "m1_" || String.sub s 0 3 = "m2_")
    then String.sub s 3 (String.length s - 3)
    else s

(* Escape backslashes and double-quotes for use inside a graphviz
 * double-quoted label string.  Other graphviz escape sequences (\n, \l)
 * are inserted deliberately and must not be double-escaped here. *)
let escape_val s =
    s |> Str.global_replace (Str.regexp_string "\\") "\\\\"
      |> Str.global_replace (Str.regexp_string "\"") "'"

(* Build the body of a double-quoted graphviz label for one state node.
 * Layout: title line (centered \n), then each state variable left-aligned (\l). *)
let node_label (state : ty bindlist) (suffix : string)
               (model_opt : (exp * exp) list option) (title : string) : string =
    let var_lines = List.map (fun db ->
        let vname = name_of_binding db ^ suffix in
        match Option.bind model_opt (fun m -> List.assoc_opt (EVar (Var vname)) m) with
        | Some v -> sp "%s = %s\\l" (name_of_binding db) (escape_val (string_of_smt v))
        | None   -> sp "%s\\l" (name_of_binding db)
    ) state in
    (* title is centered via \n; variable lines are left-aligned via \l *)
    title ^ "\\n" ^ String.concat "" var_lines

(* Write a .dot file for one commutativity query.
 *
 * model_opt: if Some m, m is an alist (EVar → value exp) for state
 *   variables that were returned by the solver.  Variables absent from m
 *   are shown with their name only (no value). *)
let generate (spec : spec) (m1 : method_spec) (m2 : method_spec)
             (model_opt : (exp * exp) list option) (result_label : string) : unit =
    let idx = !diagram_counter in
    diagram_counter := idx + 1;
    let filename = sp "servois2_diagram_%04d.dot" idx in
    let n1 = display_name m1.name in
    let n2 = display_name m2.name in
    let st = spec.state in

    let nd id title sfx =
        sp "  %s [shape=box fontname=Courier label=\"%s\"];"
           id (node_label st sfx model_opt title)
    in

    let dot = String.concat "\n" [
        "digraph {";
        sp "  label=\"Object: %s  [query %d: %s]\";" spec.name idx result_label;
        "  labelloc=t;";
        "  fontname=Courier;";
        "";
        nd "init" "Init State"                     "";
        nd "s1"   (sp "after %s"    n1)      "1";
        nd "s12"  (sp "after %s;%s" n1 n2)   "12";
        nd "s2"   (sp "after %s"    n2)      "2";
        nd "s21"  (sp "after %s;%s" n2 n1)   "21";
        "";
        sp "  init -> s1  [label=\" %s \"];" n1;
        sp "  s1   -> s12 [label=\" %s \"];" n2;
        sp "  init -> s2  [label=\" %s \"];" n2;
        sp "  s2   -> s21 [label=\" %s \"];" n1;
        sp "  s12  -> s21  [label=\" states_eq?\", style=dashed, dir=none];";
        "";
        "  { rank=same; s12; s21 }";
        "}"
    ] in
    let oc = open_out filename in
    output_string oc dot;
    output_char oc '\n';
    close_out oc;
    pfnq "Diagram written to %s\n" filename
