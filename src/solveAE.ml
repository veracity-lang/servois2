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
let generate_bowtie_ae_memo = memoize @@ fun (spec, m1, (m2, _mode)) ->
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

let generate_bowtie_ae spec m1 m2 =
    generate_bowtie_ae_memo (spec, m1, (m2, !Solve.mode))

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
    ; sp "; FORALL-EXISTS Assert NOT(commute condition => m1;m2==m2;m1)"
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
        then let scalar_state = List.filter
                 (fun db -> match snd db with TInt | TBool -> true | _ -> false)
                 spec.state in
             Diagram.state_var_exps scalar_state diagram_sfxs
        else [] in
    (* For each scalar state variable that appears as an array index in the method
       terms, emit (select heap_arr<sfx> key<sfx>) for every heap array and suffix.
       This makes heap contents at those keys visible in the SAT model. *)
    let heap_sel_exprs =
        if !Util.diagram then
            let heap_arr_names =
                List.filter_map (fun db ->
                    let n = name_of_binding db in
                    match snd db with
                    | TArray _ when
                        String.length n >= 4 && String.sub n 0 4 = "heap"
                        && n <> "heap_alloc" -> Some n
                    | _ -> None
                ) spec.state in
            let scalar_names =
                List.filter_map (fun db ->
                    let n = name_of_binding db in
                    match snd db with
                    | TInt ->
                        let is_heap = String.length n >= 4 && String.sub n 0 4 = "heap" in
                        let is_size = let l = String.length n in
                                      l >= 5 && String.sub n (l-5) 5 = "_size" in
                        if is_heap || is_size then None else Some n
                    | _ -> None
                ) spec.state in
            let rec find_keys acc = function
                | EFunc ("select", [_; EVar (Var k)]) when List.mem k scalar_names ->
                    if List.mem k acc then acc else k :: acc
                | EFunc (_, args) -> List.fold_left find_keys acc args
                | EBop (_, a, b)  -> find_keys (find_keys acc a) b
                | EUop (_, a)     -> find_keys acc a
                | ELop (_, es)    -> List.fold_left find_keys acc es
                | EITE (a, b, c)  -> find_keys (find_keys (find_keys acc a) b) c
                | ELet (bs, e)    ->
                    List.fold_left (fun a (_,b) -> find_keys a b) (find_keys acc e) bs
                | EForall (_, e) | EExists (_, e) -> find_keys acc e
                | _ -> acc
            in
            let all_terms = List.concat_map (fun m -> List.concat_map snd m.terms) [m1; m2] in
            let keys = List.fold_left find_keys [] all_terms in
            List.concat_map (fun sfx ->
                List.concat_map (fun harr ->
                    List.map (fun key ->
                        EFunc ("select", [EVar (Var (harr ^ sfx)); EVar (Var (key ^ sfx))])
                    ) keys
                ) heap_arr_names
            ) diagram_sfxs
        else [] in
    let ae_quant = match !Solve.mode with
        | Solve.RightMover -> Some Diagram.AE_Right
        | Solve.LeftMover  -> Some Diagram.AE_Left
        | Solve.Bowtie     -> Some Diagram.AE_Bowtie in
    (* Heap cells by numeric index and thread-local array snapshots, for the SVG diagram. *)
    let max_cells = 16 in
    let heap_numeric_exprs =
        if !Util.diagram then
            List.concat_map (fun sfx ->
              List.concat_map (fun i ->
                [ EFunc ("select", [EVar (Var ("heap_value" ^ sfx)); EConst (CInt i)])
                ; EFunc ("select", [EVar (Var ("heap_next"  ^ sfx)); EConst (CInt i)])
                ])
              (List.init max_cells Fun.id))
            diagram_sfxs
        else [] in
    let thread_var_name =
        let ns = List.filter_map (fun db ->
            match snd db with TInt -> Some (name_of_binding db) | _ -> None)
            spec.state in
        if List.mem "tj" ns then "tj"
        else if List.mem "ti" ns then "ti"
        else if List.mem "t"  ns then "t"
        else "" in
    let all_arr_names = List.filter_map (fun db ->
        let n = name_of_binding db in
        match snd db with
        | TArray (TInt, TInt) when n <> "heap_value" && n <> "heap_next" -> Some n
        | _ -> None) spec.state in
    (* Split into TLoc arrays (drawn as arrows) and int arrays (shown as values). *)
    let local_arr_names = List.filter (fun n -> List.mem n spec.tloc_arr_names) all_arr_names in
    let int_arr_names   = List.filter (fun n -> not (List.mem n spec.tloc_arr_names)) all_arr_names in
    (* Request model values for both TLoc and int local arrays. *)
    let local_sel_exprs =
        if !Util.diagram && thread_var_name <> "" then
            List.concat_map (fun sfx ->
              List.map (fun arr ->
                EFunc ("select",
                    [ EVar (Var (arr ^ sfx))
                    ; EVar (Var (thread_var_name ^ sfx)) ]))
              (local_arr_names @ int_arr_names))
            diagram_sfxs
        else [] in
    let global_int_names = List.filter_map (fun db ->
        let n = name_of_binding db in
        match snd db with
        | TInt when n <> "" && Char.uppercase_ascii n.[0] <> n.[0]
                    && n <> thread_var_name
                    && not (String.length n >= 4 && String.sub n 0 4 = "heap")
                    && not (let l = String.length n in l >= 5 && String.sub n (l-5) 5 = "_size") -> Some n
        | _ -> None) spec.state in
    let global_int_exprs =
        if !Util.diagram then
            List.concat_map (fun sfx ->
              List.map (fun n -> EVar (Var (n ^ sfx))) global_int_names)
            diagram_sfxs
        else [] in
    let s = string_of_smt_query_ae spec m1 m2
        (get_vals @ diagram_exprs @ heap_sel_exprs @ heap_numeric_exprs @ local_sel_exprs @ global_int_exprs)
        smt_exp in
    pfv "SMT QUERY (AE): %s\n" (string_of_smt smt_exp);
    pfvv "\n%s\n" s;
    dump_query_if_enabled s;
    flush stdout;
    let raw_lines = run_prover prover s in
    let raw = parse_prover_output prover raw_lines in
    dump_result_if_enabled (match raw with Sat _ -> "sat" | Unsat -> "unsat" | Unknown -> "unknown");
    dump_model_if_enabled raw_lines;
    if !Util.diagram then begin
        let n_d  = List.length diagram_exprs in
        let n_h  = List.length heap_sel_exprs in
        let n_hn = List.length heap_numeric_exprs in
        let n_lo = List.length local_sel_exprs in
        let n_gi = List.length global_int_exprs in
        let model_opt, heap_model_opt, svg_model_opt = match raw with
            | Sat vs ->
                (try
                    let d_vals  = List.filteri (fun i _ -> i >= n_orig && i < n_orig + n_d) vs in
                    let h_vals  = List.filteri (fun i _ -> i >= n_orig + n_d && i < n_orig + n_d + n_h) vs in
                    let hn_vals = List.filteri (fun i _ -> i >= n_orig + n_d + n_h && i < n_orig + n_d + n_h + n_hn) vs in
                    let lo_vals = List.filteri (fun i _ -> i >= n_orig + n_d + n_h + n_hn && i < n_orig + n_d + n_h + n_hn + n_lo) vs in
                    let gi_vals = List.filteri (fun i _ -> i >= n_orig + n_d + n_h + n_hn + n_lo && i < n_orig + n_d + n_h + n_hn + n_lo + n_gi) vs in
                    let scalar_model  = List.combine diagram_exprs (List.map snd d_vals) in
                    let numeric_model = List.combine (heap_numeric_exprs @ local_sel_exprs)
                                                     (List.map snd (hn_vals @ lo_vals)) in
                    let global_int_model = List.combine global_int_exprs (List.map snd gi_vals) in
                    Some scalar_model,
                    (if heap_sel_exprs = [] then None
                     else Some (List.combine heap_sel_exprs (List.map snd h_vals))),
                    Some (numeric_model @ scalar_model @ global_int_model)
                with _ -> None, None, None)
            | _ -> None, None, None
        in
        Diagram.generate spec m1 m2 model_opt heap_model_opt diagram_sfxs
            (match raw with Sat _ -> "sat" | Unsat -> "unsat" | Unknown -> "unknown")
            (string_of_smt smt_exp) ae_quant;
        (* Heap diagram SVG for SAT counterexamples *)
        (match svg_model_opt with
         | Some svg_model when thread_var_name <> "" ->
             let global_names = List.filter_map (fun db ->
                 let n = name_of_binding db in
                 match snd db with
                 | TInt when n <> "" && Char.uppercase_ascii n.[0] = n.[0]
                             && n <> thread_var_name -> Some n
                 | _ -> None) spec.state in
             let svg_titles = match !Solve.mode with
                 | Solve.RightMover ->
                     [ "Init"
                     ; sp "After %s" (Diagram.display_name m1.name)
                     ; sp "After %s; %s"
                           (Diagram.display_name m1.name)
                           (Diagram.display_name m2.name)
                     ]
                 | _ ->
                     List.map (fun sfx ->
                         sp "State %s" (if sfx = "" then "0" else sfx))
                     diagram_sfxs
             in
             Cex_svg.write_svg (outfile "heap_diagram.svg")
                 ~suffixes:diagram_sfxs
                 ~titles:svg_titles
                 ~global_names
                 ~local_arr_names
                 ~int_arr_names
                 ~global_int_names
                 ~thread_var:thread_var_name
                 svg_model
         | _ -> ())
    end;
    match raw with
    | Sat vs when diagram_exprs <> [] ->
        Sat (List.filteri (fun i _ -> i < n_orig) vs)
    | _ -> raw
