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
  }

let last_benchmarks = ref {predicates = 0; predicates_filtered = 0; smtqueries = 0; time = 0.0}

let string_of_benches benches = sp "predicates, %d\npredicates_filtered, %d\nsmtqueries, %d\ntime, %.6f" benches.predicates benches.predicates_filtered benches.smtqueries benches.time

type counterex = exp bindlist

let synth ?(options = default_synth_options) spec m n =
    let spec' = if options.lift then lift spec else spec in

    let m_spec = get_method spec m |> mangle_method_vars true in
    let n_spec = get_method spec n |> mangle_method_vars false in

    let preds = match options.preds with None -> generate_predicates spec' m_spec n_spec | Some x -> x in
    (* TODO: do predicate filtering *)
    let bench = ref { !last_benchmarks with predicates = List.length preds; predicates_filtered = List.length preds } in
    let synth_inner preds prover (timelimit : float option) spec m_spec n_spec =
      let phi = ref @@ Disj [] in
      let phi_tilde = ref @@ Disj [] in
      (* I'm pretty sure this is preferable to carrying it around in an option: *)
      let init_time = Unix.gettimeofday () in
      let answer_incomplete = ref false in
      let rec refine_wrapped h ps = try refine h ps with Failure _ -> answer_incomplete := true 
      and refine (h : conjunction) (p_set : pred list) : unit =
        let solve_inst = solve prover spec m_spec n_spec in
        let pred_smt = List.map smt_of_pred p_set in
        begin match solve_inst pred_smt @@ commute (spec.precond) h with
          | Unsat -> phi := add_disjunct h !phi
          | Unknown -> raise @@ Failure "commute failure" (* TODO: Better error behavior? Backtracking? *)
          | Sat s -> begin let com_cex = parse_pred_data s in
            match solve_inst pred_smt @@ non_commute (spec.precond) h with
              | Unsat -> phi_tilde := add_disjunct h !phi_tilde
              | Unknown -> raise @@ Failure "non_commute failure"
              | Sat s -> begin let non_com_cex = parse_pred_data s in
                let p = !choose { solver = solve_inst; spec = spec; h = h; choose_from = p_set; cex_ncex = (com_cex, non_com_cex) } in
                    refine_wrapped (add_conjunct (atom_of_pred p) h) (remove p p_set);
                    refine_wrapped (add_conjunct (not_atom @@ atom_of_pred p) h) (remove p p_set)
                end
            end
        end in
      let init_smt_queries = !Provers.n_queries in
      begin try begin match timelimit with None -> run | Some f -> run_with_time_limit f end (fun () -> refine (Conj []) (List.sort (fun x y -> complexity x - complexity y) @@ preds)) 
          with
              | Timeout f -> pfv "Time limit of %.6fs exceeded.\n" f; answer_incomplete := true
      end;
      bench := { !bench with
          smtqueries = !Provers.n_queries - init_smt_queries;
          time = Float.sub (Unix.gettimeofday ()) init_time };
      if !answer_incomplete then pfv "Warning: Answer incomplete.\n" else ();
      !phi, !phi_tilde in
    let ret = synth_inner preds options.prover options.timeout spec' m_spec n_spec in
    last_benchmarks := !bench; ret
  
