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
  ; mc_run_time: float
  ; lattice_construct_time: float
  }

let last_benchmarks = ref {predicates = 0; 
                           predicates_filtered = 0; 
                           smtqueries = 0; 
                           time = 0.0; 
                           synth_time = 0.0;
                           mc_run_time = 0.0;
                           lattice_construct_time = 0.0}

let string_of_benches benches = sp 
    "predicates, %d\npredicates_filtered, %d\nsmtqueries, %d\nlattice_construct_time, %.6f\ntime_mc_run, %.6f\ntime_synth, %.6f\ntime, %.6f" 
    benches.predicates 
    benches.predicates_filtered 
    benches.smtqueries
    benches.lattice_construct_time
    benches.mc_run_time
    benches.synth_time
    benches.time        

type counterex = exp bindlist

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


let synth ?(options = default_synth_options) spec m n =
  let init_time = Unix.gettimeofday () in  
  let init_smt_queries = !Provers.n_queries in
  let lattice_construct_time = ref 0.0 in

  let spec = if options.lift then lift spec else spec in
  let m_spec = get_method spec m |> mangle_method_vars true in
  let n_spec = get_method spec n |> mangle_method_vars false in

  let state_vars = spec.state @ (m_spec.args) @ (n_spec.args) in

  let preds_unfiltered = match options.preds with
    | None -> generate_predicates spec m_spec n_spec
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
  Precond_synth.mc_run_args := (preds, state_vars);
  let module PS = Precond_synth in 
  let module L = PS.L in
  let ps, pps, pequivc, l = if options.lattice then begin
      let start = Unix.gettimeofday () in
      let ps_, pps_, pequivc_ = Predicate_analyzer.observe_rels preds state_vars in
      Predicate_analyzer_logger.log_predicate_implication_chains ps_ pps_;
      let l_ = PS.construct_lattice ps_ pps_ in
      lattice_construct_time := (Unix.gettimeofday ()) -. start;
      ps_, pps_, pequivc_, l_ end 
    else
      (* make trivial lattice *)
      [], [], [], PS.construct_lattice (List.map (fun p -> P p) preds) []
  in

  let synth_start_time = Unix.gettimeofday () in

  seq (last_benchmarks :=
     { predicates = List.length preds_unfiltered
     ; predicates_filtered = List.length preds
     ; smtqueries = !Provers.n_queries - init_smt_queries
     ; time = Float.sub (Unix.gettimeofday ()) init_time 
     ; synth_time = (Unix.gettimeofday ()) -. synth_start_time -. !Precond_synth.mc_run_time
     ; mc_run_time = !Precond_synth.mc_run_time
     ; lattice_construct_time = !lattice_construct_time }) @@

  let answer_incomplete = ref false in
  let phi = ref @@ Disj [] in
  let phi_tilde = ref @@ Disj [] in

  let solve_inst = solve options.prover spec m_spec n_spec in

  (* Choose (maybe?) strongest predicates amongst the ones that differentiate
        or (maybe?) peak the one with the highest rank amongst the same differentiating ones
     1. verify the validity of commute or non_commute formulas
     2. if they hold, disjoin it with the formula
     3. if they don't hold, then explore the predicates in the lattice obtained 
        after removing the upperset of the chosen predicate
     4. continue in DFS manner
  *)

  (* preh is the h of the last iteration, maybep is Some predicate that was added last iteration. *)
  let rec refine_wrapped preh maybep l = 
    try refine preh maybep l with Failure _ -> answer_incomplete := true
  and refine: conjunction -> predP option -> predP L.el L.t -> unit = 
    fun preh maybep l -> 
    let p_set = L.list_of l in
    let pred_smt = List.map exp_of_predP p_set in
    let h = match maybep with
      | None -> preh
      | Some p -> add_conjunct (exp_of_predP p) preh
    in
    
    begin match solve_inst pred_smt @@ commute spec h with
      | Unsat -> 
        pfv "\nPred found for phi: %s\n" 
          (string_of_smt @@ smt_of_conj h);
        phi := add_disjunct h !phi
      | Unknown -> raise @@ Failure "commute failure"
      | Sat vs -> 
        let com_cex = pred_data_of_values vs in
        begin match solve_inst pred_smt @@ non_commute spec h with
          | Unsat ->
            pfv "\nPred found for phi-tilde: %s\n" 
              (string_of_smt @@ smt_of_conj h);
            phi_tilde := add_disjunct h !phi_tilde
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
                     (List.map (fun p -> string_of_predP p) (L.upperset_of_v p l))); 
                (add_conjunct (exp_of_predP p) preh), L.remove_upperset p l 
            end in
            (* find the equivalent of non p *)
            let p_lattice = if options.lattice then PS.pfind p pequivc l else p in
            let nonp_lattice = if options.lattice then PS.pfind (negate p) pequivc l else (negate p) in
            let l = L.remove p_lattice l |> L.remove nonp_lattice in
            refine_wrapped preh (Some p_lattice) l;
            refine_wrapped preh (Some nonp_lattice) l
        end 
    end
  in

  begin try (
    match options.timeout with 
    | None -> run 
    | Some f -> run_with_time_limit f
  ) (fun () -> 
      refine_wrapped (Conj []) None l
    ) 
    with Timeout -> 
      pfv "Time limit of %.6fs exceeded.\n" (Option.get options.timeout); 
      answer_incomplete := true
  end;

  if !answer_incomplete then pfv "Warning: Answer incomplete.\n";
  !phi, !phi_tilde
