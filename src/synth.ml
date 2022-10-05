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
  ; lattice : bool
  }

let default_synth_options =
  { preds = None
  ; prover = (module Provers.ProverCVC4)
  ; lift = true
  ; timeout = None
  ; lattice = false
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
(*
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
    
    let rec refine_wrapped h ps = try refine h ps with Failure _ -> answer_incomplete := true 
    and refine (h : conjunction) (p_set : pred list) : unit =
        let solve_inst = solve options.prover spec m_spec n_spec in
        let pred_smt = List.map smt_of_pred p_set in
        begin match solve_inst pred_smt @@ commute spec h with
            | Unsat -> phi := add_disjunct h !phi
            | Unknown -> raise @@ Failure "commute failure"
            | Sat vs -> 
            let com_cex = pred_data_of_values vs in
            begin match solve_inst pred_smt @@ non_commute spec h with
                | Unsat -> phi_tilde := add_disjunct h !phi_tilde
                | Unknown -> raise @@ Failure "non_commute failure"
                | Sat vs ->
                let non_com_cex = pred_data_of_values vs in
                let p = !choose { solver = solve_inst; spec = spec; h = h; choose_from = p_set; cex_ncex = (com_cex, non_com_cex) } in
                    refine_wrapped (add_conjunct (atom_of_pred p) h) (remove p p_set);
                    refine_wrapped (add_conjunct (not_atom @@ atom_of_pred p) h) (remove p p_set)
            end
        end
    in
    
    begin try (match options.timeout with None -> run | Some f -> run_with_time_limit f) (fun () -> 
        refine_wrapped (Conj []) (List.sort (fun x y -> complexity x - complexity y) @@ preds)
        ) with Timeout -> pfv "Time limit of %.6fs exceeded.\n" (Option.get options.timeout); answer_incomplete := true
    end;
    
    if !answer_incomplete then pfv "Warning: Answer incomplete.\n";
    
    !phi, !phi_tilde
*)

(* refine with new variant of CHOOSE alg
   1. input:
      psmcs: list of pairs of predicate and the corresponding split ratio
      pps:   list of implication relation of any two predicates
   2. implement backtracking algorithm, 
      * at each step, generate the next candidates in the ranking order and 
        perform a depth-first search
      * when a predicate that leads to a valid commute or not_commute is reached,
      backtrack to the previous prefix of the conjunction and 
      take only the complement branch of the last concluding predicate, discarding the others
      
   Start with True as the initial guess and recursively explore predicates until the 
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


let synth_with_mc ?(options = default_synth_options) spec m n =
  let init_time = Unix.gettimeofday () in
  let init_smt_queries = !Provers.n_queries in

  let spec = if options.lift then lift spec else spec in
  let m_spec = get_method spec m |> mangle_method_vars true in
  let n_spec = get_method spec n |> mangle_method_vars false in

  let state_vars = spec.state @ (m_spec.args) @ (n_spec.args) in

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
  let ps, pps, pequivc = Predicate_analyzer.observe_rels preds state_vars in
  Predicate_analyzer_logger.log_predicate_implication_chains ps pps;          
  let module PS = Precond_synth in 
  let module L = PS.L in
  let l = if options.lattice
    then 
      let psmcs = Predicate_analyzer.run_mc preds state_vars 
                  |> List.filter (fun (p, _) -> List.exists ((=) p) ps) in
      PS.construct_lattice psmcs pps 
    else
      (* make trivial lattice *)
      PS.construct_lattice (List.map (fun p -> (P p, 0.0)) preds) []
  in

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

  (* Choose (maybe?) strongest predicates amongst the ones that differentiate
        or (maybe?) peak the one with the highest rank amongst the same differentiating ones
     1. verify the validity of commute or non_commute formulas
     2. if they hold, then do a DFS to find the weakest predicates that keep the
        validity of formula
     3. if they don't hold, then explore the predicates in the lattice obtained 
        after removing the upperset of the chosen predicate
     4. continue in DFS manner
  *)
  let weakerps fn_commute h_prefix minp l = 
    let rec foldl f ps l acc =
      match ps with
      | [] -> acc 
      | p::ps' ->       
        let p_cbys = L.coveredbyset p l in
        begin match p_cbys with
          | [] -> foldl f ps' l (f p acc)
          | _ -> 
            let acc' = foldl f p_cbys l acc in
            match acc' with
            | [] -> f p acc'
            | _ -> acc'
        end
    in
    let commutef p acc = 
      let p_ = fst p in 
      let h_ = add_conjunct (exp_of_predP p_) h_prefix in
      match solve_inst [] @@ fn_commute spec h_ with
        | Unsat ->
          pfv "\nWeaker predicate found: %s" (string_of_predP p_);
          p_::acc 
        | Unknown -> raise @@ Failure "commute failure"
        | Sat _ -> acc
    in
    match foldl commutef (L.coveredbyset minp l) l [] with
    | [] -> [fst minp]
    | wps -> wps
  in

  let rec refine_ppeak_wrapped preh maybep l = 
    try refine_ppeak preh maybep l with Failure _ -> answer_incomplete := true
  and refine_ppeak: conjunction -> (predP * float) option -> (predP * float) L.el L.t -> unit = 
    fun preh maybep l -> 
    let p_set = List.map fst (L.list_of l) in
    let pred_smt = List.map exp_of_predP p_set in
    let h = match maybep with
      | None -> preh
      | Some p -> add_conjunct (exp_of_predP (fst p)) preh
    in
    
    begin match solve_inst pred_smt @@ commute spec h with
      | Unsat -> 
        begin match maybep with
          | None ->
             pfv "\nPartial solution for phi: %s\n" 
               (string_of_smt @@ smt_of_conj h);
            phi := add_disjunct h !phi
          | Some p -> 
            pfv "\nPred found for phi: %s" (string_of_predP (fst p));
            let wps = weakerps commute preh p l in
            pfv "\nWeakers predicates found for phi: [%s]"
              (String.concat " ; " (List.map (string_of_predP) wps));
            List.iter (fun p_ ->
                let p' = exp_of_predP p_ in
                let h' = add_conjunct p' preh in
                pfv "\nPartial solution for phi: %s\n" 
                  (string_of_smt @@ smt_of_conj h');
                phi := add_disjunct h' !phi
              ) wps
        end
      | Unknown -> raise @@ Failure "commute failure"
      | Sat vs -> 
        let com_cex = pred_data_of_values vs in
        begin match solve_inst pred_smt @@ non_commute spec h with
          | Unsat ->
            begin match maybep with
              | None ->
                 pfv "\nPartial solution for phi-tilde: %s\n" 
                   (string_of_smt @@ smt_of_conj h);
                 phi_tilde := add_disjunct h !phi_tilde
              | Some p -> 
                pfv "\nPred found for phi-tilde: %s" (string_of_predP (fst p));
                let wps = weakerps non_commute preh p l in
                pfv "\nWeakers predicates found for phi-tilde: [%s]"
                  (String.concat " ; " (List.map (string_of_predP) wps));
                List.iter (fun p_ ->
                    let p' = exp_of_predP p_ in
                    let h' = add_conjunct p' preh in
                    pfv "\nPartial solution for phi-tilde: %s\n" 
                      (string_of_smt @@ smt_of_conj h');
                    phi_tilde := add_disjunct h' !phi_tilde) wps
            end
          | Unknown -> raise @@ Failure "non_commute failure"
          | Sat vs -> 
            let non_com_cex = pred_data_of_values vs in
            let p = !choose { solver = solve_inst; spec = spec; h = h; choose_from = l; cex_ncex = (com_cex, non_com_cex) }
            in
            (* current p is not concluding, then 
               - add it to preh, and 
               - remove all its upper set (which comprises weaker predicates)      
            *)
            let preh, l = begin match maybep with
              | None -> preh, l
              | Some p ->
                pfv "\nUpperset removed: [%s]\n" 
                  (String.concat " ; " 
                     (List.map (fun p -> string_of_predP @@ fst p) (L.upperset_of_v p l))); 
                (add_conjunct (exp_of_predP (fst p)) preh), L.remove_upperset p l 
            end in
            (* find the equivalent of non p *)
            let p_lattice = if options.lattice then PS.pfind p pequivc l else (p, 0.0) in
            let nonp_lattice = if options.lattice then PS.pfind (negate p) pequivc l else (negate p, 0.0) in
            let l = L.remove p_lattice l |> L.remove nonp_lattice in
            refine_ppeak_wrapped preh (Some p_lattice) l;
            refine_ppeak_wrapped preh (Some nonp_lattice) l
        end 
    end
  in

  begin try (
    match options.timeout with 
    | None -> run 
    | Some f -> run_with_time_limit f
  ) (fun () -> 
      refine_ppeak_wrapped (Conj []) None l
    ) 
    with Timeout -> 
      pfv "Time limit of %.6fs exceeded.\n" (Option.get options.timeout); 
      answer_incomplete := true
  end;

  if !answer_incomplete then pfv "Warning: Answer incomplete.\n";
  !phi, !phi_tilde

let synth = synth_with_mc
