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
  ; stronger_predicates_first: bool
  }

let default_synth_options =
  { preds = None
  ; prover = (module Provers.ProverCVC4)
  ; lift = true
  ; timeout = None
  ; lattice = false
  ; stronger_predicates_first = false
  }

type benches =
  { predicates : int
  ; predicates_filtered : int
  ; predicates_in_lattice: int
  ; smtqueries : int
  ; mcqueries : int
  ; time : float
  ; synth_time : float
  ; mc_run_time: float
  ; lattice_construct_time: float
  }

let last_benchmarks = ref {predicates = 0; 
                           predicates_filtered = 0;
                           predicates_in_lattice = 0;
                           smtqueries = 0;
                           mcqueries = 0;
                           time = 0.0; 
                           synth_time = 0.0;
                           mc_run_time = 0.0;
                           lattice_construct_time = 0.0}

let string_of_benches benches = sp 
    "predicates, %d\npredicates_filtered, %d\npredicates_in_lattice, %d\nsmtqueries, %d\nmcqueries, %d\ntime_lattice_construct, %.6f\ntime_mc_run (part of time_synth), %.6f\ntime_synth, %.6f\ntime, %.6f" 
    benches.predicates 
    benches.predicates_filtered 
    benches.predicates_in_lattice
    benches.smtqueries
    benches.mcqueries
    benches.lattice_construct_time
    benches.mc_run_time
    benches.synth_time
    benches.time        

type counterex = exp bindlist

let synth ?(options = default_synth_options) spec m n =
  let init_time = Unix.gettimeofday () in  
  let init_smt_queries = !Provers.n_queries in
  let init_mc_queries = !Model_counter.n_queries in
  let lattice_construct_time = ref 0.0 in

  let spec = if options.lift then lift spec else spec in
  let m_spec = get_method spec m |> mangle_method_vars true in
  let n_spec = get_method spec n |> mangle_method_vars false in

  let preds_unfiltered = match options.preds with
    | None -> generate_predicates spec m_spec n_spec
    | Some x -> x in
  let preds = filter_predicates options.prover spec m_spec n_spec preds_unfiltered in
  
  let construct_lattice ps pps = 
    Choose.order_rels_set := pps;
    let l = L.construct ps in
    pfv "\n\nLATTICE:\n%s" (L.string_of l);
    l
  in
  
  let ps, pps, pequivc, l = if options.lattice then begin
      (* One-time analysis of predicates: 
         1.Get all predicates generated from specs. 
           Append their negated form to the set of candidates
         2.Find all pairs (p1, p2) s.t. p1 => p2
         3.Construct the lattice *)
      let start = Unix.gettimeofday () in
      let ps_, pps_, pequivc_ = Predicate_analyzer.observe_rels 
          options.prover spec m_spec n_spec preds in
      Predicate_analyzer_logger.log_predicate_implication_chains ps_ pps_;
      let l_ = construct_lattice ps_ pps_ in
      lattice_construct_time := (Unix.gettimeofday ()) -. start;
      ps_, pps_, pequivc_, l_ end 
    else
      (* make trivial lattice *)
      [], [], [], construct_lattice (List.map (fun p -> P p) preds) []
  in

  let pfind p pequivc l =
      let ps' = List.find (fun ps -> List.mem p ps) pequivc in
      match List.fold_right (fun p res ->
          match res with
          | Some _ -> res
          | None -> L.find_opt ((=) p) l 
        ) ps' None with
      | Some pr -> pr
      | None -> raise @@ Failure (sp "Predicate %s not found" (string_of_predP p))
  in

  let synth_start_time = Unix.gettimeofday () in

  seq (last_benchmarks :=
     { predicates = 2 * (List.length preds_unfiltered)
     ; predicates_filtered = 2 * (List.length preds)
     ; predicates_in_lattice = if options.lattice then L.length l else 0
     ; smtqueries = !Provers.n_queries - init_smt_queries
     ; mcqueries = !Model_counter.n_queries - init_mc_queries
     ; time = Float.sub (Unix.gettimeofday ()) init_time 
     ; synth_time = (Unix.gettimeofday ()) -. synth_start_time
     ; mc_run_time = !Choose.mc_run_time
     ; lattice_construct_time = !lattice_construct_time }) @@

  let answer_incomplete = ref false in
  let phi = ref @@ Disj [] in
  let phi_tilde = ref @@ Disj [] in

  let solve_inst = solve options.prover spec m_spec n_spec in

  let env = {
    solver = solve_inst;
    spec = spec;
    m_spec = m_spec;
    n_spec = n_spec;
    h = Conj [];
    choose_from = l;
    choose_stronger_predicates = options.stronger_predicates_first;
    cex_ncex = ([], [])
  } in

  let rec refine_wrapped h l = 
    try refine h l with Failure _ -> answer_incomplete := true
  and refine (h : conjunction) (l : predP L.el L.t) : unit = 
    let p_set = L.list_of l in
    let pred_smt = List.map exp_of_predP p_set in
    
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
            let p = !choose { env with h = h; choose_from = l; cex_ncex = (com_cex, non_com_cex) } in
            let neg_p = negate p in
            (* Find lattice keys *)
            let p_lattice = if options.lattice then pfind p pequivc l else p in
            let negp_lattice = if options.lattice then pfind neg_p pequivc l else neg_p in
            let l' = l |> L.remove p_lattice |> L.remove negp_lattice in
            (* current p is not concluding, then remove its upper set (which comprises weaker predicates) *)
            let l_pos = L.remove_upperset p l' |>
              seq @@ pfv "\nUpperset removed: [%s]\n" (String.concat " ; " 
              (List.map string_of_predP @@ L.upperset_of_v p l'))
            in
            let l_neg = L.remove_upperset neg_p l' |>
              seq @@ pfv "\nUpperset removed: [%s]\n" (String.concat " ; " 
              (List.map string_of_predP @@ L.upperset_of_v neg_p l'))
            in
            refine_wrapped (add_conjunct (exp_of_predP p) h) l_pos;
            refine_wrapped (add_conjunct (exp_of_predP neg_p) h) l_neg
        end 
    end
  in

  begin try (
    match options.timeout with 
    | None -> run 
    | Some f -> run_with_time_limit f
  ) (fun () -> 
      refine_wrapped (Conj []) l
    ) 
    with Timeout -> 
      pfv "Time limit of %.6fs exceeded.\n" (Option.get options.timeout); 
      answer_incomplete := true
  end;

  if !answer_incomplete then pfv "Warning: Answer incomplete.\n";
  !phi, !phi_tilde
