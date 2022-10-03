(* Module for conducting the phi synthesis algorithm 
 * Algorithm comes from Fig. 1 of TACAS'18.
 *)

open Util
open Smt
open Solve
open Spec
open Phi
open Provers
open Choose
open Smt_parsing
open Predicate

type synth_options =
  { preds : pred list option
  ; prover : (module Prover)
  ; lift : bool
  ; timeout : float option
  }

let default_synth_options =
  { preds = None
  ; prover = (module Provers.ProverCVC4)
  ; lift = true
  ; timeout = None
  }

type benches =
  { predicates : int
  ; predicates_filtered : int
  ; smtqueries : int
  ; time : float
  ; synth_time : float
  }

let last_benchmarks = ref {predicates = 0; 
                           predicates_filtered = 0; 
                           smtqueries = 0; 
                           time = 0.0; 
                           synth_time = 0.}

let string_of_benches benches = sp 
    "predicates, %d\npredicates_filtered, %d\nsmtqueries, %d\ntime, %.6f, \ntime_synth, %.6f" 
    benches.predicates 
    benches.predicates_filtered 
    benches.smtqueries 
    benches.time
    benches.synth_time

type counterex = exp bindlist

let synth ?(options = default_synth_options) spec m n =
    let init_time = Unix.gettimeofday () in
    let init_smt_queries = !Provers.n_queries in
    let spec = if options.lift then lift spec else spec in

    let m_spec = get_method spec m |> mangle_method_vars true in
    let n_spec = get_method spec n |> mangle_method_vars false in

    let preds_unfiltered = match options.preds with None -> generate_predicates spec m_spec n_spec | Some x -> x in
    let preds = filter_predicates options.prover spec m_spec n_spec preds_unfiltered in

    let synth_start_time = Unix.gettimeofday () in
    
    seq (last_benchmarks := 
      { predicates = List.length preds_unfiltered
      ; predicates_filtered = List.length preds
      ; smtqueries = !Provers.n_queries - init_smt_queries
      ; time = Float.sub (Unix.gettimeofday ()) init_time 
      ; synth_time = Float.sub (Unix.gettimeofday ()) synth_start_time }) @@
      
    let phi = ref @@ Disj [] in
    let phi_tilde = ref @@ Disj [] in
    let answer_incomplete = ref false in
    
    let rec refine_wrapped h ps cont = try refine h ps cont with Failure _ -> answer_incomplete := true 
    and refine (h : conjunction) (p_set : pred list) (cont : unit -> unit) : unit =
        let solve_inst = solve options.prover spec m_spec n_spec in
        let pred_smt = List.map smt_of_pred p_set in
        begin match solve_inst pred_smt @@ commute spec h with
            | Unsat -> phi := add_disjunct h !phi; cont ()
            | Unknown -> raise @@ Failure "commute failure"
            | Sat vs -> 
            let com_cex = pred_data_of_values vs in
            begin match solve_inst pred_smt @@ non_commute spec h with
                | Unsat -> phi_tilde := add_disjunct h !phi_tilde; cont ()
                | Unknown -> raise @@ Failure "non_commute failure"
                | Sat vs ->
                let non_com_cex = pred_data_of_values vs in
                let p = !choose { solver = solve_inst; spec = spec; h = h; choose_from = p_set; cex_ncex = (com_cex, non_com_cex) } in
                    refine_wrapped (add_conjunct (atom_of_pred p) h) (remove p p_set) @@ compose (fun () -> refine_wrapped (add_conjunct (not_atom @@ atom_of_pred p) h) (remove p p_set) id) cont
            end
        end
    in
    
    begin try (match options.timeout with None -> run | Some f -> run_with_time_limit f) (fun () -> 
        refine_wrapped (Conj []) (List.sort (fun x y -> complexity x - complexity y) @@ preds) id
        ) with Timeout -> pfv "Time limit of %.6fs exceeded.\n" (Option.get options.timeout); answer_incomplete := true
    end;
    
    if !answer_incomplete then pfv "Warning: Answer incomplete.\n";
    
    !phi, !phi_tilde

(* refine with new variant of CHOOSE alg
   1. input:
      psmcs: list of pairs of predicate and the corresponding split ratio
      pps:   list of implication relation of any two predicates
   2. implement backtracking algorithm, 
      * at each step, generate the next candidates in the ranking order and 
        perform a depth-first search
      * when a predicate that leads to a valid commute or not_commute is reached,
      backtrack to the previous prefix of the conjunction and 
      take only the complement branch of the last "deciding" predicate, discarding the others
      
   Start with True as the initial "guess" and recursively explore predicates until the 
   assertion holds or is refuted universally
   At each call:  
   (1) if the final assertion equally holds and does not hold, i.e., we get 
       counterexamples for both cases of valid and refuted assertion, then
       - run the set of predicates on the satisfying / unsatisfying models, 
         and filter out the predicates failing to differentiate them
       - pick the predicate that has the highest rank and explore it
       - remove the predicate from lattice and pass the smaller lattice
       - recursively call the procedure with the new predicate appended to the conjunction
         in the context of the smaller lattice  
   (2) If the final assertion either universally holds or doesn not nold, 
       then continue with the following steps:
       - add the conjunction as a partial solution to the final solution  
         (which is a disjunction of partial solutions)                            
       - next, (a) mark the last predicate (node) and  
               (b) backtrack to the previous predicate (node), 
               (c) discard any candidates that aren't the equivalent of the negated marked 
                   predicate, and consider only the negated predicate if found 
*)
let synth_with_mc ?(options = default_synth_options) spec m n state_vars maximize_cover =
   let init_time = Unix.gettimeofday () in
   let init_smt_queries = !Provers.n_queries in

   let spec = if options.lift then lift spec else spec in
   let m_spec = get_method spec m |> mangle_method_vars true in
   let n_spec = get_method spec n |> mangle_method_vars false in

   let preds_unfiltered = match options.preds with
     | None ->
       let preds = generate_predicates spec m_spec n_spec in
       preds
     | Some x -> x in
   let preds = filter_predicates options.prover spec m_spec n_spec preds_unfiltered in

    (* One-time analysis of predicates: 
       1. Get all predicates generated from specs. 
          Append their negated form to the set of candidates
       2. Find all pairs (p1, p2) s.t. p1 => p2
       3. Run the model counter on all predicates
       4. Annotate each predicate with the corresponding split ratio distance from 0.5
       5. Construct the lattice 
    *)
   let ps, pps, pequivc = Predicate_analyzer.observe_rels_all preds state_vars in
   Predicate_analyzer_logger.log_predicate_implication_chains ps pps;          
   let psmcs = Predicate_analyzer.run_mc preds state_vars |> List.filter (fun (p, _) -> List.exists ((=) p) ps) in
   let module PS = Precond_synth in 
   let module L = PS.L in
   let rank_pred = 
     if maximize_cover then PS.compare_pred_maximum_cover
     else PS.compare_pred_bisect
   in
   let l = PS.construct_lattice psmcs pps in

   let synth_start_time = Unix.gettimeofday () in

   seq (last_benchmarks :=
      { predicates = List.length preds_unfiltered
      ; predicates_filtered = List.length preds
      ; smtqueries = !Provers.n_queries - init_smt_queries
      ; time = Float.sub (Unix.gettimeofday ()) init_time 
      ; synth_time = Float.sub (Unix.gettimeofday ()) synth_start_time}) @@

   let answer_incomplete = ref false in
   let phi = ref @@ Disj [] in
   let phi_tilde = ref @@ Disj [] in
  

  let solve_inst = solve options.prover spec m_spec n_spec in

  let rec refine_ppeak_wrapped h l = 
    try refine_ppeak h l with Failure _ -> answer_incomplete := true; false 
  and refine_ppeak (h : conjunction) (l : (predP * float) L.el L.t) : bool =
    let p_set = List.map fst  (L.list_of l) in
    let pred_smt = List.map exp_of_predP p_set in
    
    begin match solve_inst pred_smt @@ commute spec h with
      | Unsat ->
        pfv "\nPartial solution for phi: %s\n" 
          (string_of_smt @@ smt_of_conj h);
        phi := add_disjunct h !phi; 
        true
      | Unknown -> raise @@ Failure "commute failure"
      | Sat vs -> 
        let com_cex = pred_data_of_values vs in
        begin match solve_inst pred_smt @@ non_commute spec h with
          | Unsat -> 
            pfv "\nPartial solution for phi-tilde: %s\n" 
              (string_of_smt @@ smt_of_conj h);
            phi_tilde := add_disjunct h !phi_tilde;
            true
          | Unknown -> raise @@ Failure "non_commute failure"
          | Sat vs ->
            let non_com_cex = pred_data_of_values vs in
            let candidates = PS.gen_next_candidates l rank_pred (com_cex, non_com_cex)  in
            
            Precond_synth.print_pred_candidates candidates;
            let rec pnext l ps = 
              match ps with
              | [] -> []
              | p::ps' -> 
                let l' = L.remove p l in
                (p, l')::(pnext l' ps')
            in
            (*
            ignore @@ List.fold_left (fun res ((p_, d_), l_) ->
                let handle_next = fun () ->
                  let new_ps = List.map fst (L.list_of l_) in
                  Predicate_analyzer_logger.log_ppeak_result (p_, d_) new_ps;
                  let h_ = add_conjunct (exp_of_predP p_) h in
                  pfv "\n\nNew predicate added to conjunction: %s\n" 
                    (string_of_smt @@ smt_of_conj h_);
                  (refine_ppeak_wrapped h_ l_, Some p_)
                in
                match res with
                | false, _ -> handle_next ()
                | true, Some pp ->
                  if PS.pequiv pequivc p_ (negate pp) then handle_next ()
                  else  res
                | true, None -> raise @@ Failure "Unexpected. Unreachable statement reached"
              ) (false, None) (pnext l candidates);
            *)
            
            begin match pnext l candidates with
            | ((p_, d_), l_) :: ps -> let new_ps = List.map fst (L.list_of l_) in
                  Predicate_analyzer_logger.log_ppeak_result (p_, d_) new_ps;
                  let h_ = add_conjunct (exp_of_predP p_) h in
                  pfv "\n\nNew predicate added to conjunction: %s\n" 
                    (string_of_smt @@ smt_of_conj h_);
                  ignore @@ refine_ppeak_wrapped h_ l_;
                  ignore @@ refine_ppeak_wrapped (add_conjunct (exp_of_predP @@ negate p_) h) l_
            | [] -> raise @@ Failure "No remaining predicates." end;
            false
        end
    end
  in

  begin try (
    match options.timeout with 
    | None -> run 
    | Some f -> run_with_time_limit f
  ) (fun () -> 
      ignore(refine_ppeak_wrapped (Conj []) l)
    ) 
    with Timeout -> 
      pfv "Time limit of %.6fs exceeded.\n" (Option.get options.timeout); 
      answer_incomplete := true
  end;

  if !answer_incomplete then pfv "Warning: Answer incomplete.\n";
  !phi, !phi_tilde

