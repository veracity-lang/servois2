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

(* Generates variable declarations, oper_ae, and bowtie_ae for an AE query.
 *
 * Three modes (driven by !Solve.mode):
 *
 *   RightMover  ∀(m1;m2) ∃(m2;m1)
 *     free: "1","12"   exists: "2","21"
 *     assert oper_m1m2;  bowtie = ∃(2,21) oper_m2m1 ∧ equal(12,21)
 *
 *   LeftMover   ∀(m2;m1) ∃(m1;m2)
 *     free: "2","21"   exists: "1","12"
 *     assert oper_m2m1;  bowtie = ∃(1,12) oper_m1m2 ∧ equal(12,21)
 *
 *   Bowtie      ∀(m1;m2) ∧ ∀(m2;m1),  both have existential witnesses
 *     free: "1","12","2","21"   exists: "w2","w21" and "w1","w12"
 *     assert oper_m1m2 ∧ oper_m2m1
 *     bowtie = (∃(w2,w21) oper_m2m1_w ∧ equal(12,w21))
 *            ∧ (∃(w1,w12) oper_m1m2_w ∧ equal(w12,21))
 *)
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

    let m1args_name = List.map fst (List.map (first string_of_var) m1.args) in
    let m2args_name = List.map fst (List.map (first string_of_var) m2.args) in

    let postcond_datanames = List.sort String.compare (find_vars spec.postcond) in
    let postcond_args_list sfx args =
        String.concat " " (List.map (fun a -> a ^ sfx) postcond_datanames @ args) in

    let vars_ref = ref "" in
    let (^=) r s = r := !r ^ s in

    let decl_state_vars sfxs =
        iter_prod (fun db e -> vars_ref ^= mk_var (name_of_binding db ^ e) (snd db))
            spec.state sfxs in
    let decl_result_vars sfx ret_list =
        List.iteri (fun i ret -> vars_ref ^= mk_var (sp "result_%d_%s" i sfx) ret) ret_list in

    let oper_xy pre_sfx post_sfx (m : method_spec) args =
        sp "  (%s_pre_condition %s)\n  (%s_post_condition %s)"
            m.name (pre_args_list pre_sfx args)
            m.name (post_args_list pre_sfx post_sfx args m.ret)
    in

    (* Build (exists (...)) binding list for the given state suffixes and result suffixes. *)
    let mk_exists_bindings state_sfxs m2_ret_sfx m1_ret_sfx =
        List.concat_map (fun db ->
            List.map (fun sfx -> sp "(%s %s)" (name_of_binding db ^ sfx) (string_of_ty (snd db)))
                state_sfxs
        ) spec.state
        @ List.mapi (fun i ret -> sp "(result_%d_%s %s)" i m2_ret_sfx (string_of_ty ret)) (List.map snd m2.ret)
        @ List.mapi (fun i ret -> sp "(result_%d_%s %s)" i m1_ret_sfx (string_of_ty ret)) (List.map snd m1.ret)
    in

    let post_clause sfx =
        if String.equal (postcond_args_list sfx []) ""
        then "  postcondition"
        else sp "  (postcondition %s)" (postcond_args_list sfx [])
    in

    (* Standard result-equality lines: m1 results match, m2 results match. *)
    let result_eqs m1_sfx_a m1_sfx_b m2_sfx_a m2_sfx_b =
        List.mapi (fun i _ -> sp "  (= result_%d_%s result_%d_%s)" i m1_sfx_a i m1_sfx_b) m1.ret
      @ List.mapi (fun i _ -> sp "  (= result_%d_%s result_%d_%s)" i m2_sfx_a i m2_sfx_b) m2.ret
    in

    (* One-armed exists body: oper(pre→mid→post) ∧ result equalities ∧ postcond ∧ states_equal *)
    let mk_exists_body pre_sfx mid_sfx post_sfx
                       (m_first : method_spec) first_args
                       (m_second : method_spec) second_args
                       m1_free_sfx m1_exists_sfx m2_free_sfx m2_exists_sfx
                       equal_sfx_a equal_sfx_b =
        [ "  (and"
        ; oper_xy pre_sfx  mid_sfx  m_first  first_args
        ; oper_xy mid_sfx  post_sfx m_second second_args
        ]
        @ result_eqs m1_free_sfx m1_exists_sfx m2_free_sfx m2_exists_sfx
        @ [ post_clause post_sfx
          ; sp "  (states_equal %s %s)"
                (pre_args_list equal_sfx_a []) (pre_args_list equal_sfx_b [])
          ; "))"
          ]
    in

    (match !Solve.mode with
    | Solve.RightMover ->
        (* free: "1","12";  assert oper(m1;m2);  exists: "2","21" *)
        decl_state_vars ["1"; "12"];
        decl_result_vars "1"  (List.map snd m1.ret);
        decl_result_vars "12" (List.map snd m2.ret)
    | Solve.LeftMover ->
        (* ∀(m2;m1): m2 → "1", m1 → "12";  ∃(m1;m2): m1 → "2", m2 → "21" *)
        decl_state_vars ["1"; "12"];
        decl_result_vars "1"  (List.map snd m2.ret);   (* m2 runs first *)
        decl_result_vars "12" (List.map snd m1.ret)
    | Solve.Bowtie ->
        (* free: "1","12","2","21";  assert both opers;  exists: "w2"/"w21" and "w1"/"w12" *)
        decl_state_vars ["1"; "12"; "2"; "21"];
        decl_result_vars "1"  (List.map snd m1.ret);
        decl_result_vars "12" (List.map snd m2.ret);
        decl_result_vars "2"  (List.map snd m2.ret);
        decl_result_vars "21" (List.map snd m1.ret));

    let vars = !vars_ref in

    let oper_m1m2 = unlines ["(assert (and"; oper_xy "" "1" m1 m1args_name;
                                              oper_xy "1" "12" m2 m2args_name; "))"] in
    let oper_m2m1 = unlines ["(assert (and"; oper_xy "" "2" m2 m2args_name;
                                              oper_xy "2" "21" m1 m1args_name; "))"] in
    (* LeftMover universal: m2 first to "1", m1 second to "12" *)
    let oper_m2_m1_via_12 = unlines ["(assert (and"; oper_xy "" "1" m2 m2args_name;
                                                      oper_xy "1" "12" m1 m1args_name; "))"] in

    let bowtie_ae = match !Solve.mode with
        | Solve.RightMover ->
            let eb = mk_exists_bindings ["2"; "21"] "2" "21" in
            unlines @@
            [ "(define-fun m1m2_bowtie_ae () Bool"
            ; sp "  (exists (%s)" (String.concat " " eb) ]
            @ mk_exists_body "" "2" "21" m2 m2args_name m1 m1args_name
                "1" "21" "12" "2" "12" "21"
            @ ["  )"]

        | Solve.LeftMover ->
            (* exists: m1 (foo) "" → "2", m2 (bar) "2" → "21"
             * result sfxs: m1_free="12" m1_exists="2"  m2_free="1" m2_exists="21" *)
            let eb = mk_exists_bindings ["2"; "21"] "21" "2" in
            unlines @@
            [ "(define-fun m1m2_bowtie_ae () Bool"
            ; sp "  (exists (%s)" (String.concat " " eb) ]
            @ mk_exists_body "" "2" "21" m1 m1args_name m2 m2args_name
                "12" "2" "1" "21" "12" "21"
            @ ["  )"]

        | Solve.Bowtie ->
            let eb_right = mk_exists_bindings ["w2"; "w21"] "w2" "w21" in
            let eb_left  = mk_exists_bindings ["w1"; "w12"] "w12" "w1" in
            let right_body = mk_exists_body "" "w2" "w21" m2 m2args_name m1 m1args_name
                "1" "w21" "12" "w2" "12" "w21" in
            let left_body  = mk_exists_body "" "w1" "w12" m1 m1args_name m2 m2args_name
                "21" "w1" "2" "w12" "w12" "21" in
            unlines @@
            [ "(define-fun m1m2_bowtie_ae () Bool (and"
            ; sp "  (exists (%s)" (String.concat " " eb_right) ]
            @ right_body
            @ [ sp "  (exists (%s)" (String.concat " " eb_left) ]
            @ left_body
            @ [ "))"]
    in

    let opers = match !Solve.mode with
        | Solve.RightMover -> oper_m1m2
        | Solve.LeftMover  -> oper_m2_m1_via_12
        | Solve.Bowtie     -> unlines [oper_m1m2; oper_m2m1]
    in

    unlines ~trailing_newline:false [vars; opers; bowtie_ae]

let smt_bowtie_ae = EVar (Var "m1m2_bowtie_ae")

(* AE commutativity:     smt → m1m2_bowtie_ae
 * (oper_ae is asserted as a hard constraint in generate_bowtie_ae,
 *  so the counterexample query is: oper_ae ∧ smt ∧ ¬m1m2_bowtie_ae) *)
let commute_ae_of_smt smt = EBop (Imp, smt, smt_bowtie_ae)
let commute_ae   spec h   = smt_of_conj (add_conjunct spec.precond h) |> commute_ae_of_smt

let non_commute_ae_of_smt smt = EBop (Imp, smt, EUop (Not, smt_bowtie_ae))
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
    (* Only free-variable states are requestable; exists-bound states are not in the model *)
    (* Left and right mover both have free "1","12" and exists "2","21" *)
    let diagram_sfxs = match !Solve.mode with
        | Solve.RightMover | Solve.LeftMover -> [""; "1"; "12"]
        | Solve.Bowtie                       -> [""; "1"; "12"; "2"; "21"] in
    let diagram_exprs =
        if !Util.diagram
        then Diagram.state_var_exps spec.state diagram_sfxs
        else [] in
    let ae_quant = match !Solve.mode with
        | Solve.RightMover -> Some Diagram.AE_Right
        | Solve.LeftMover  -> Some Diagram.AE_Left
        | Solve.Bowtie     -> Some Diagram.AE_Bowtie in
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
            (match raw with Sat _ -> "sat" | Unsat -> "unsat" | Unknown -> "unknown") ae_quant
    end;
    match raw with
    | Sat vs when diagram_exprs <> [] ->
        Sat (List.filteri (fun i _ -> i < n_orig) vs)
    | _ -> raw
