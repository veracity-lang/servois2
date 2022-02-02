(* Module for interfacing with theorem provers *)


open Util
open Smt
open Spec
open Provers
open Phi

(* TODO: Maybe have a data type that keeps track of needed elements like *)
(* 
type smt_query = {
    spec : spec option;
    bowtie : (method_spec * method_spec) option;
    smt_exp : exp
}
This allows for extensions like determinism etc. Currently assumes we always need the spec and bowtie.
*)

(* This will create the entire SMT string to send to a prover.
 * It will engage with lots of features of SMT which are
 * abstracted away from the actual "smt" module.
 * It'll include the variable declarations, function declarations, etc. *)
let smt_string_of_spec (spec : spec) (state_constraints : exp) : string =
  raise @@ Failure "smt_string_of_spec"


let make_new = function
    | (Var s, ty) -> (VarPost s, ty)
    | (VarPost _, _) -> raise @@ Failure "New-ing a post variable."
let make_new_bindings = List.map make_new

let define_fun (name : string) (args : ty bindlist) (r_ty : ty) (def : exp) : string =
    "(define-fun " ^
    name ^ "\n" ^
    "  ( " ^ String.concat "\n    " (List.map (fun (v, ty) -> sp "(%s %s)" (string_of_var v) (string_of_ty ty)) args) ^ " )\n" ^
    "  " ^ string_of_ty r_ty ^ "\n" ^
    "  " ^ Str.global_replace (Str.regexp_string "\n") "\n  " (String.trim @@ string_of_smt def) ^ "\n" ^
    " )\n"

let smt_of_spec spec = (* TODO: Preamble? *)
    let s = spec.state in
    ";; BEGIN: smt_of_spec " ^ spec.name ^ "\n\n" ^
    begin match spec.preamble with
        | Some s -> s ^ "\n"
        | None -> "" end ^
    define_fun "states_equal" (s @ make_new_bindings s) TBool spec.state_eq ^ "\n" ^
    String.concat "" (List.map (fun (m : method_spec) ->
        let s_old = s in let s_new = make_new_bindings s in
        define_fun (m.name ^ "_pre_condition") (s_old @ m.args) TBool m.pre ^ "\n" ^
        define_fun (m.name ^ "_post_condition") (s_old @ m.args @ s_new @ m.ret) TBool m.post ^ "\n"
    ) spec.methods) ^
    ";; END: smt_of_spec " ^ spec.name ^ "\n"

let generate_bowtie spec m1 m2 = 
    let (datanames : string list) = List.map name_of_binding spec.state in
    let mk_var name ty = "(declare-fun " ^ name ^ " () " ^ string_of_ty ty ^ ")\n" in
    let pre_args_list postfix (argslist : string list) = String.concat " " (List.map (fun a -> a ^ postfix) datanames @ argslist) in
    let post_args_list old_postfix new_postfix argslist ret = String.concat " "
        (List.map (fun a -> a ^ old_postfix) datanames @
         argslist @
         List.map (fun a -> a ^ new_postfix) datanames @
         List.mapi (fun i _ -> sp "result_%d_" i ^ new_postfix) ret) in
    let m1args_binding = List.map (first string_of_var) m1.args in
    let m1args_name = List.map fst m1args_binding in
    let m2args_binding = List.map (first string_of_var) m2.args in (* TODO: If m1, m2 have the same arg names? *)
    let m2args_name = List.map fst m2args_binding in
    (uncurry mk_var |> flip List.map (m1args_binding @ m2args_binding) |> String.concat "") ^
    let err_state = has_err_state spec in
    let oper_xy x y (m : method_spec) args = let mname = m.name in "  (" ^ mname ^ "_pre_condition " ^ pre_args_list x args ^ ")\n" ^
        "  (" ^ mname ^ "_post_condition " ^ post_args_list x y args m.ret ^ ")\n" in
    List.fold_left (fun acc_outer databinding -> 
        acc_outer ^ List.fold_left (fun acc_inner e ->
            acc_inner ^ mk_var (name_of_binding databinding ^ e) (snd databinding)) "" [""; "1"; "2"; "12"; "21"]
        ) "" spec.state ^
    (* TODO: What if result is in datanames? *)
    (let tmp = ref "" in List.iteri (fun i ret -> tmp := !tmp ^ mk_var ("result_" ^ string_of_int i ^ "_1") (snd ret) ^ mk_var ("result_" ^ string_of_int i ^ "_21") (snd ret)) m1.ret; !tmp) ^
    (let tmp = ref "" in List.iteri (fun i ret -> tmp := !tmp ^ mk_var ("result_" ^ string_of_int i ^ "_2") (snd ret) ^ mk_var ("result_" ^ string_of_int i ^ "_12") (snd ret)) m2.ret; !tmp) ^
    "(define-fun oper () Bool (and \n" ^
    oper_xy "" "1" m1 m1args_name ^
    oper_xy "2" "21" m1 m1args_name ^
    oper_xy "" "2" m2 m2args_name ^
    oper_xy "1" "12" m2 m2args_name ^
    begin if err_state (* TODO: bowtie vs left/right movers *) 
        then "  (or (not err12) (not err21))"
        else "" end ^
    "))\n" ^
    (* TODO: deterministic, complete *)
    "(define-fun bowtie () Bool (and  \n   " ^ 
    (*List.fold_left (fun acc k -> acc ^ "(= result_" ^ string_of_int k ^ "_1 result_" ^ string_of_int k ^ "_21)\n   ") "" (flip List.init succ @@ List.length m1.ret) ^
    List.fold_left (fun acc k -> acc ^ "(= result_" ^ string_of_int k ^ "_2 result_" ^ string_of_int k ^ "_12)\n   ") "" (flip List.init succ @@ List.length m2.ret) ^
    *)
    (let tmp = ref "" in
    List.iteri (fun i _ -> tmp := !tmp ^ sp "(= result_%d_1 result_%d_21)\n   " i i) m1.ret;
    List.iteri (fun i _ -> tmp := !tmp ^ sp "(= result_%d_2 result_%d_12)\n   " i i) m2.ret;
    !tmp) ^
    "   (states_equal " ^
    pre_args_list "12" [] ^ " " ^ pre_args_list "21" [] ^ ")\n" ^
    "))\n"

let string_of_smt_query spec m1 m2 get_vals smt_exp = (* The query used in valid *)
    "(set-logic ALL_SUPPORTED)\n" ^
    smt_of_spec spec ^
    generate_bowtie spec m1 m2 ^
    sp "(assert (not %s))\n" (string_of_smt smt_exp) ^
    "(check-sat)\n" ^
    if null get_vals then "" else sp "(get-value (%s))\n" (String.concat " " @@ List.map string_of_smt get_vals)

let smt_bowtie = EVar(Var("bowtie"))
let smt_oper = EVar(Var("oper"))

let non_commute precond h = EBop(Imp, smt_of_conj @@ (add_conjunct smt_oper @@ add_conjunct precond h), EUop(Not, smt_bowtie))
let commute precond h = EBop(Imp, smt_of_conj @@ (add_conjunct smt_oper @@ add_conjunct precond h), smt_bowtie)

let solve (prover : (module Prover)) (spec : spec) (m1 : method_spec) (m2 : method_spec) (get_vals : exp list) (smt_exp : exp) : solve_result =
  let s = string_of_smt_query spec m1 m2 get_vals smt_exp in
  let module P = (val prover) in
  epfv "%s\n" s;
  P.run s
