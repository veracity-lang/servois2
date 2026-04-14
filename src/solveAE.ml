(* Module for AE (forall-exists) commutativity checking.
 *
 * Checks whether, for every execution of m1;m2 from some initial state,
 * there EXISTS an execution of m2;m1 from the same initial state that
 * reaches a states_equal final state (and returns equal results).
 *
 * This is strictly weaker than the standard AA commutativity in Solve.ml,
 * which requires ALL m2;m1 executions to reach an equal state.
 *
 * SMT encoding:
 *   - m1;m2-path variables are declared free (universally quantified by
 *     SMT refutation): state suffixes "1", "12"; result_i_1, result_i_12.
 *     The initial state (no suffix) is already declared by Solve.smt_of_spec.
 *   - m2;m1-path variables appear inside an SMT-LIB (exists ...) in
 *     bowtie_ae: state suffixes "2", "21"; result_i_2, result_i_21.
 *
 * A query is SAT iff there is a counterexample to AE commutativity:
 * an m1;m2 execution from which no m2;m1 execution reaches an equal state.
 *)

open Util
open Smt
open Spec
open Provers
open Phi

let mk_var name ty = "(declare-fun " ^ name ^ " () " ^ string_of_ty ty ^ ")\n"

(* Generates variable declarations, oper_ae, and bowtie_ae for an AE query. *)
let generate_bowtie_ae = curry3 @@ memoize @@ fun (spec, m1, m2) ->
    let datanames = List.map name_of_binding spec.state in
    let pre_args_list sfx args =
        String.concat " " (List.map (fun a -> a ^ sfx) datanames @ args) in
    let post_args_list old_sfx new_sfx args ret =
        String.concat " "
            (  List.map (fun a -> a ^ old_sfx) datanames
             @ args
             @ List.map (fun a -> a ^ new_sfx) datanames
             @ List.mapi (fun i _ -> sp "result_%d_" i ^ new_sfx) ret) in

    let m1args_name =
        let m1args_binding = List.map (first string_of_var) m1.args in
        List.map fst m1args_binding in
    let m2args_name =
        let m2args_binding = List.map (first string_of_var) m2.args in
        List.map fst m2args_binding in

    let postcond_datanames = List.sort String.compare (find_vars spec.postcond) in
    let postcond_args_list sfx args =
        String.concat " " (List.map (fun a -> a ^ sfx) postcond_datanames @ args) in

    let vars_ref = ref "" in
    let (^=) r s = r := !r ^ s in

    (* Declare free (m1;m2-path) intermediate state variables.
     * Initial state (no suffix) is already declared in Solve.smt_of_spec. *)
    iter_prod
        (fun db e -> vars_ref ^= mk_var (name_of_binding db ^ e) (snd db))
        spec.state ["1"; "12"];
    List.iteri (fun i ret -> vars_ref ^= mk_var (sp "result_%d_1"  i) ret) (List.map snd m1.ret);
    List.iteri (fun i ret -> vars_ref ^= mk_var (sp "result_%d_12" i) ret) (List.map snd m2.ret);

    let vars = !vars_ref in

    let oper_xy pre_sfx post_sfx (m : method_spec) args =
        sp "  (%s_pre_condition %s)\n  (%s_post_condition %s)"
            m.name (pre_args_list pre_sfx args) m.name (post_args_list pre_sfx post_sfx args m.ret)
    in

    (* Variables existentially quantified in bowtie_ae: the m2;m1 intermediate
     * states and return values. *)
    let exists_bindings =
        List.concat_map
            (fun db -> List.map
                (fun sfx -> sp "(%s %s)" (name_of_binding db ^ sfx) (string_of_ty (snd db)))
                ["2"; "21"])
            spec.state
        @ List.mapi (fun i ret -> sp "(result_%d_2  %s)" i (string_of_ty ret)) (List.map snd m2.ret)
        @ List.mapi (fun i ret -> sp "(result_%d_21 %s)" i (string_of_ty ret)) (List.map snd m1.ret)
    in

    (* Postcondition applied to the m1;m2 final state (free variable s12). *)
    let post_clause =
        if String.equal (postcond_args_list "12" []) ""
        then "  postcondition"
        else sp "  (postcondition %s)" (postcond_args_list "12" [])
    in

    (* bowtie_ae: there exists a m2;m1 execution reaching a state equal to s12 *)
    let bowtie_ae = unlines @@
        [ "; For all m1;m2 ... "
        ; "(assert (and"
        ; oper_xy ""  "1"  m1 m1args_name
        ; oper_xy "1" "12" m2 m2args_name
        ; "))"
        ; "; Exists m2;m1 ... "
        ; "(define-fun m1m2_bowtie_ae () Bool"
        ; sp "  (exists (%s)" (String.concat " " exists_bindings)
        ; "  (and"
        ; oper_xy ""  "2"  m2 m2args_name
        ; oper_xy "2" "21" m1 m1args_name
        ]
        @ List.mapi (fun i _ -> sp "  (= result_%d_1  result_%d_21)" i i) m1.ret
        @ List.mapi (fun i _ -> sp "  (= result_%d_2  result_%d_12)" i i) m2.ret
        @ [ post_clause
          ; sp "  (states_equal %s %s)"
                (pre_args_list "12" []) (pre_args_list "21" [])
          ; ")))"
          ]
    in

    unlines ~trailing_newline:false [vars; bowtie_ae]

let smt_bowtie_ae = EVar (Var "m1m2_bowtie_ae")

(* AE commutativity condition: (oper_ae /\ smt) -> m1m2_bowtie_ae *)
let commute_ae_of_smt commute_cond = EBop (Imp, commute_cond, smt_bowtie_ae)
let commute_ae   spec h     = smt_of_conj (add_conjunct spec.precond h) |> commute_ae_of_smt

(* AE non-commutativity condition: (oper_ae /\ smt) -> ¬m1m2_bowtie_ae *)
let non_commute_ae_of_smt commute_cond = EBop (Imp, commute_cond, EUop (Not, smt_bowtie_ae))
let non_commute_ae spec h     = smt_of_conj (add_conjunct spec.precond h) |> non_commute_ae_of_smt

let string_of_smt_query_ae spec m1 m2 get_vals smt_exp =
    unlines @@
    [ "(set-logic ALL)"
    ; "(define-fun havoc  ( (vpre Int) (vpost Int) ) Bool true)"
    ; Solve.smt_of_spec spec
    ; generate_bowtie_ae spec m1 m2
    ; sp "; Assert NOT(commute condition => m1;m2==m2;m1)"
    ; sp "(assert (not %s))" (string_of_smt smt_exp)
    ; "(check-sat)"]
    @ if null get_vals then []
      else [sp "(get-value (%s))" (String.concat " " @@ List.map string_of_smt get_vals)]

let solve_ae (prover : (module Prover)) (spec : spec) (m1 : method_spec) (m2 : method_spec)
             (get_vals : exp list) (smt_exp : exp) : solve_result =
    let n_orig = List.length get_vals in
    (* Only the free-variable states are requestable; "2"/"21" are inside exists *)
    let diagram_exprs =
        if !Util.diagram
        then Diagram.state_var_exps spec.state [""; "1"; "12"]
        else [] in
    let s = string_of_smt_query_ae spec m1 m2 (get_vals @ diagram_exprs) smt_exp in
    pfv "SMT QUERY (AE): %s\n" (string_of_smt smt_exp);
    pfvv "\n%s\n" s;
    dump_query_if_enabled s;
    flush stdout;
    let raw = run_prover prover s |> parse_prover_output prover in
    if !Util.diagram then begin
        let model_opt = match raw with
            | Sat vs ->
                (try
                    let n_d = List.length diagram_exprs in
                    let d_vals = List.filteri (fun i _ -> i >= n_orig && i < n_orig + n_d) vs in
                    Some (List.combine diagram_exprs (List.map snd d_vals))
                with _ -> None)
            | _ -> None
        in
        Diagram.generate spec m1 m2 model_opt
            (match raw with Sat _ -> "sat" | Unsat -> "unsat" | Unknown -> "unknown")
    end;
    match raw with
    | Sat vs when diagram_exprs <> [] ->
        Sat (List.filteri (fun i _ -> i < n_orig) vs)
    | _ -> raw
