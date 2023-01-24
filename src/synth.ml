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
  ; no_cache : bool
  ; stronger_predicates_first: bool
  }

let default_synth_options =
  { preds = None
  ; prover = (module Provers.ProverCVC4)
  ; lift = true
  ; timeout = None
  ; lattice = false
  ; no_cache = false
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
  ; answer_incomplete : bool
  ; n_atoms : int
  }

let default_bench = {predicates = 0; 
                   predicates_filtered = 0;
                   predicates_in_lattice = 0;
                   smtqueries = 0;
                   mcqueries = 0;
                   time = 0.0; 
                   synth_time = 0.0;
                   mc_run_time = 0.0;
                   lattice_construct_time = 0.0;
                   answer_incomplete = false;
                   n_atoms = 0}
  
let last_benchmarks = ref default_bench

let string_of_benches benches = sp 
    "predicates, %d\npredicates_filtered, %d\npredicates_in_lattice, %d\nsmtqueries, %d\nmcqueries, %d\ntime_lattice_construct, %.6f\ntime_mc_run (part of time_synth), %.6f\ntime_synth, %.6f\ntime, %.6f\nanswer_incomplete, %b\nn_atoms, %d" 
    benches.predicates 
    benches.predicates_filtered 
    benches.predicates_in_lattice
    benches.smtqueries
    benches.mcqueries
    benches.lattice_construct_time
    benches.mc_run_time
    benches.synth_time
    benches.time
    benches.answer_incomplete
    benches.n_atoms

type counterex = exp bindlist

type synth_env = {phi : disjunction ref; phi_tilde : disjunction ref; synth_start_time : float option ref; bench : benches ref}

let rec synth ?(options = default_synth_options) spec m n =

  let init_smt_queries = !Provers.n_queries in
  let init_mc_queries = !Model_counter.n_queries in
  let phi = ref @@ Disj [] in
  let phi_tilde = ref @@ Disj [] in
  let bench = ref default_bench in
  let synth_start_time = ref None in
  let init_time = Unix.gettimeofday () in

  seq (last_benchmarks := { !bench with
       smtqueries = !Provers.n_queries - init_smt_queries
     ; mcqueries = !Model_counter.n_queries - init_mc_queries
     ; time = Float.sub (Unix.gettimeofday ()) init_time
     ; synth_time = begin match !synth_start_time with | Some f -> (Unix.gettimeofday ()) -. f | _ -> 0. end
     ; mc_run_time = !Choose.mc_run_time 
     ; n_atoms = n_atoms_of !phi}) @@
  
  begin try (
    match options.timeout with 
    | None -> run
    | Some f -> run_with_time_limit f
  ) (fun () ->
      synth_inner {phi; phi_tilde; synth_start_time; bench}
        options spec m n
    ) 
    with Timeout -> 
      pfnq "Time limit of %.6fs exceeded.\n" (Option.get options.timeout); 
      bench := {!bench with answer_incomplete = true}
  end;

  if !bench.answer_incomplete then pfnq "Warning: Answer incomplete.\n";
  !phi, !phi_tilde
  
and synth_inner env options spec m n =

  let unlifted_spec = spec in 
  let spec = if options.lift then lift spec else spec in
  let m_spec = get_method spec m |> mangle_method_vars true in
  let n_spec = get_method spec n |> mangle_method_vars false in

  let preds_unfiltered = match options.preds with
    | None -> begin 
      let m_spec2 = get_method unlifted_spec m |> mangle_method_vars true in
      let n_spec2 = get_method unlifted_spec n |> mangle_method_vars false in
      generate_predicates unlifted_spec [m_spec2; n_spec2]
    end
    | Some x -> x in
  env.bench := { !(env.bench) with predicates = List.length preds_unfiltered };
  
  let preds = filter_predicates options.prover spec preds_unfiltered in
  env.bench := { !(env.bench) with predicates_filtered = List.length preds };
  
  let construct_lattice ps pps = 
    Choose.order_rels_set := pps;
    let l = L.construct (List.sort (fun x y -> complexity x - complexity y) ps) in
    pfv "\n\nLATTICE:\n%s" (L.string_of l);
    l
  in
  
  let lattice_start_time = Unix.gettimeofday () in
  let pequivc, l = if options.lattice then begin
      (* check for a previous lattice construction, and 
         - if found, load lattice from disk
         - if not found, construct it and save it to disk
      *)
      let lattice_fname = sp "%s.lattice" spec.name in
      let equivc_fname = sp "%s.equivc" spec.name in
      if Sys.file_exists lattice_fname && Sys.file_exists equivc_fname && not options.no_cache
      then begin
        let inc = open_in lattice_fname in
        let l_ = L.load inc in
        close_in inc;
        let inc = open_in equivc_fname in
        let pequivc_ = Predicate_analyzer.load_equivc inc in
        close_in inc;
        Predicate_analyzer_logger.log_predicates_equiv_classes "Equiv classes loaded from disk"
          pequivc_;
        pfv "\nLattice loaded from disk: \n%s" (L.string_of l_);
        pequivc_, l_
      end else begin
        (* One-time analysis of predicates: 
           1.Get all predicates generated from specs. 
             Append their negated form to the set of candidates
           2.Find all pairs (p1, p2) s.t. p1 => p2
           3.Construct the lattice *)        
        let ps_, pps_, pequivc_ = Predicate_analyzer.observe_rels 
            options.prover spec preds in
        let l_ = construct_lattice ps_ pps_ in
        Predicate_analyzer_logger.log_predicate_implication_chains (L.chains_of l_);
        (if not options.no_cache then
        let outc = open_out lattice_fname in
        L.save l_ outc; close_out outc;
        let outc = open_out equivc_fname in
        Predicate_analyzer.save_equivc outc pequivc_; close_out outc else ());
        pequivc_, l_
      end
    end else
      (* make trivial lattice *)
      [], construct_lattice (List.map (fun p -> P p) preds) []
  in
  let lattice_construct_time = (Unix.gettimeofday ()) -. lattice_start_time in
  env.bench := { !(env.bench) with predicates_in_lattice = if options.lattice then L.length l else 0;
                                 lattice_construct_time = lattice_construct_time};
  
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

  env.synth_start_time := Some(Unix.gettimeofday ());

  let solve_inst = solve options.prover spec m_spec n_spec in

  let choose_env = {
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
    try refine h l with Failure _ -> env.bench := {!(env.bench) with answer_incomplete = true}
  and refine (h : conjunction) (l : predP L.el L.t) : unit = 
    let p_set = L.list_of l in
    let pred_smt = List.map exp_of_predP p_set in
    
    begin match solve_inst pred_smt @@ commute spec h with
      | Unsat ->         
        pfv "\nPred found for phi: %s\n" 
          (string_of_smt @@ smt_of_conj h);
        env.phi := add_disjunct h !(env.phi)
      | Unknown -> raise @@ Failure "commute failure"
      | Sat vs -> 
        let com_cex = pred_data_of_values vs in
        begin match solve_inst pred_smt @@ non_commute spec h with
          | Unsat ->
            pfv "\nPred found for phi-tilde: %s\n" 
              (string_of_smt @@ smt_of_conj h);
            env.phi_tilde := add_disjunct h !(env.phi_tilde)
          | Unknown -> raise @@ Failure "non_commute failure"
          | Sat vs -> 
            let non_com_cex = pred_data_of_values vs in
            let p = !choose { choose_env with h = h; choose_from = l; cex_ncex = (com_cex, non_com_cex) } in
            let neg_p = negate p in
            (* Find lattice keys *)
            let p_lattice = if options.lattice then pfind p pequivc l else p in
            let negp_lattice = if options.lattice then pfind neg_p pequivc l else neg_p in
            let l' = l |> L.remove_v p_lattice |> L.remove_v negp_lattice in
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
  refine_wrapped (Conj []) l
