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

Currently this is handled by these local refs (eg see mode)
*)

type mode = Bowtie | LeftMover | RightMover

let mode = ref Bowtie

let define_fun (name : string) (args : ty bindlist) (r_ty : ty) (def : exp) : string =
    unlines [
        sp "(define-fun %s" name;
        sp "  ( %s )" @@ String.concat "\n    " (List.map string_of_ty_binding args);
        "  " ^ string_of_ty r_ty;
        "  " ^ Str.global_replace (Str.regexp_string "\n") "\n  " (String.trim @@ string_of_smt def);
        ")"]

let smt_of_spec = memoize @@ fun spec ->
    let s = spec.state in
    unlines ~trailing_newline:false @@ [
        sp ";; BEGIN: smt_of_spec " ^ spec.name;
        ""] @
        begin match spec.preamble with
            | Some s -> [s]
            | None -> [] end @ [
        define_fun "states_equal" (s @ make_new_bindings s) TBool spec.state_eq] @
        (List.map (fun (m : method_spec) ->
            let s_old = s in let s_new = make_new_bindings s in
            sp "%s\n%s"
                (define_fun (m.name ^ "_pre_condition") (s_old @ m.args) TBool m.pre)
                (define_fun (m.name ^ "_post_condition") (s_old @ m.args @ s_new @ m.ret) TBool m.post)
            ) spec.methods) @ [
        ";; END: smt_of_spec " ^ spec.name]

let generate_bowtie = curry3 @@ memoize @@ fun (spec, m1, m2) ->
    let (datanames : string list) = List.map name_of_binding spec.state in
    let mk_var name ty = "(declare-fun " ^ name ^ " () " ^ string_of_ty ty ^ ")\n" in
    let pre_args_list postfix (argslist : string list) = String.concat " " (List.map (fun a -> a ^ postfix) datanames @ argslist) in
    let post_args_list old_postfix new_postfix argslist ret = String.concat " "
        (List.map (fun a -> a ^ old_postfix) datanames @
         argslist @
         List.map (fun a -> a ^ new_postfix) datanames @
         List.mapi (fun i _ -> sp "result_%d" i ^ new_postfix) ret) in
    let err_state = has_err_state spec in
    let m1args_binding = List.map (first string_of_var) m1.args in
    let m1args_name = List.map fst m1args_binding in
    let m2args_binding = List.map (first string_of_var) m2.args in
    let m2args_name = List.map fst m2args_binding in
    
    let vars_ref = ref "" in
    let (^=) s1 s2 = s1 := !s1 ^ s2 in
    
    (* Make a variable for each argument *)
    vars_ref ^= (uncurry mk_var |> Fun.flip List.map (m1args_binding @ m2args_binding) |> String.concat "");
    
    (* Make a variable for each state variable for each needed object *)
    iter_prod (fun databinding e -> vars_ref ^= mk_var (name_of_binding databinding ^ e) (snd databinding))
        spec.state ["_l"; "_r"; "_l1"; "_r2"; "_l12"; "_r21"];
    (* TODO: What if result is in datanames? *)
    
    (* Make results for m1, then m2, for each of the times we call them in the diamond. *)
    List.iteri (fun i ret ->
        vars_ref ^= mk_var (sp "result_%d_l1" i) ret ^ mk_var (sp "result_%d_r21" i) ret
        ) @@ List.map snd m1.ret;
    List.iteri (fun i ret ->
        vars_ref ^= mk_var (sp "result_%d_r2" i) ret ^ mk_var (sp "result_%d_l12" i) ret
        ) @@ List.map snd m2.ret;
    
    let vars = !vars_ref in
    
    (* Add in the assertions for pre-post relations. *)
    let oper_xy x y (m : method_spec) args =
        let mname = m.name in
        sp "  (%s_pre_condition %s)\n  (%s_post_condition %s)"
            mname (pre_args_list x args) mname (post_args_list x y args m.ret)
    in
    let oper = unlines @@
        [ "(define-fun oper () Bool (and "
        ; oper_xy "_l" "_l1" m1 m1args_name
        ; oper_xy "_r2" "_r21" m1 m1args_name
        ; oper_xy "_r" "_r2" m2 m2args_name
        ; oper_xy "_l1" "_l12" m2 m2args_name
        ] @
    (* Add in which end error states are allowed. *)
        begin if err_state
        then "  (and (not err_l) (not err_r))" :: (* TODO: Not very elegant or robust? *)
            [begin match !mode with
            | Bowtie -> "  (or (not err_l12) (not err_r21))"
            | LeftMover -> "  (not err_r21)"
            | RightMover -> "  (not err_l12)"
            end]
        else [] end @
        ["))"]
    in
    
    (* TODO: deterministic, complete? *)
    let bowtie = unlines @@
        [ "(define-fun bowtie () Bool (and" ] @ 
        List.mapi (fun i _ -> sp "   (= result_%d_l1 result_%d_r21)" i i) m1.ret @
        List.mapi (fun i _ -> sp "   (= result_%d_r2 result_%d_l12)" i i) m2.ret @
        [ sp "   (states_equal %s %s)" (pre_args_list "_l12" []) (pre_args_list "_r21" [])
        ; "))"
        ]
    in
    
    unlines ~trailing_newline:false [vars; oper; bowtie]

let string_of_smt_query spec m1 m2 get_vals smt_exp = (* The query used in valid *)
    unlines @@
    [ "(set-logic ALL_SUPPORTED)"
    ; smt_of_spec spec
    ; generate_bowtie spec m1 m2
    ; sp "(assert (not %s))" (string_of_smt smt_exp)
    ; "(check-sat)"] @
    if null get_vals
        then []
        else [sp "(get-value (%s))" (String.concat " " @@ List.map string_of_smt get_vals)]

let smt_bowtie = EVar(Var("bowtie"))
let smt_oper = EVar(Var("oper"))

let commute_hypothesis spec h = smt_of_conj @@ (add_conjunct smt_oper @@ add_conjunct spec.precond h)
let non_commute spec h = EBop(Imp, commute_hypothesis spec h, EUop(Not, smt_bowtie))
let commute spec h = EBop(Imp, commute_hypothesis spec h, smt_bowtie)

let solve (prover : (module Prover)) (spec : spec) (m1 : method_spec) (m2 : method_spec) (get_vals : exp list) (smt_exp : exp) : solve_result =
  let s = string_of_smt_query spec m1 m2 get_vals smt_exp in
  pfv "SMT QUERY: %s\n" (string_of_smt smt_exp);
  pfvv "\n%s\n" s;
  run_prover prover s |> parse_prover_output prover

let filter_predicates (prover : (module Prover)) spec m1 m2 (preds : pred list) =
    let query e = sp "(push 1)(assert (not %s))(check-sat)(pop 1)" (string_of_smt e) in

    let full_input = unlines @@
        [ "(set-logic ALL_SUPPORTED)"
        ; smt_of_spec spec
        ; generate_bowtie spec m1 m2] @
        List.concat_map (fun p -> let e = smt_of_pred p in
            [query e; query (EUop(Not, e))]) preds in
    
    let out = run_prover prover full_input in
    
    if List.length out != 2*List.length preds
        then failwith "filter_predicates";
    
    List.filteri (fun i _ -> List.nth out (2*i) = "sat" && List.nth out (2*i+1) = "sat") preds
