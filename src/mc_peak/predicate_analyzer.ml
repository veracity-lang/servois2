open Provers
open Model_counter
open Smt
open Spec
open Util

type 'a maybeRes = Exn of string | Val of 'a 

module type PredicateAnalyzerSig = 
sig
  val run_mc: pred list -> (string * string list) list -> (pred * mc_result * mc_result) list
  val observe_rels: pred list -> (string * string list) list -> (predP * predP * int) list
  val verify_antichain: predP list -> (string * string list) list -> (predP * predP) list
end

module PredicateAnalyzer: PredicateAnalyzerSig = 
struct
 
  let prover: (module Prover) = (module Provers.ProverCVC4)

  let pred_rel_set: pred list -> (pred -> predP) * (pred -> predP) -> (predP * predP) list = 
    fun ps (liftp1, liftp2)->
    (* let ps = List.filteri (fun i p -> i < 30) ps in *)
    let aps = List.mapi (fun i p -> (i, p)) ps 
    in aps 
       |> List.fold_left (
         fun acc (i, p) -> 
           (List.fold_left (
               fun acc' (j, p') ->
                 if (i < j) then
                   (liftp1 p, liftp2 p') :: acc'
                 else acc'
             ) acc aps)
       ) []

  let string_of_smt_vars: (string * string list) list  -> string = fun sorted_vars ->
    List.fold_left (fun acc (sort, vars) -> 
        List.fold_left (fun acc' var -> 
            (Printf.sprintf "(declare-fun %s () %s)" var sort)::acc'
          ) acc vars) [] sorted_vars |> String.concat "\n"

   let observe_rels: pred list -> (string * string list) list -> (predP * predP * int) list = 
    fun ps vars -> 
    let impl_rels: pred list -> (pred -> predP) * (pred -> predP) -> (predP * predP * int) list = 
      fun ps (liftp1, liftp2) -> 
        pred_rel_set ps (liftp1, liftp2) 
        |> fun pps -> 
        let pred_rel p1 p2 = ELop (Smt.Or, [exp_of_predP (negate p1); exp_of_predP p2]) in
        let query_rel e = sp "(push 1)(assert (not %s))(check-sat)(pop 1)" (string_of_smt e) in
        let string_of_smt_query = unlines ~trailing_newline: true ([
            "(set-logic ALL)";
            string_of_smt_vars vars] @ 
            (List.map (fun (p1, p2) -> 
                 let e = pred_rel p1 p2 
                 in query_rel e
               ) pps)) 
        in
        pfvv "\nPRED RELS >>> \n%s\n" string_of_smt_query;
        flush stdout;
        let out = Provers.run_prover prover string_of_smt_query in
        if List.length out != (List.length pps) 
        then failwith "eval_predicates_rels";
        List.mapi(fun i (p1, p2) -> 
            let pp_sat_res = List.nth out i in
            if (pp_sat_res = "unsat") then (p1, p2, 0)
            else if (pp_sat_res = "sat") then (p1, p2, 1) 
            else (p1, p2, -1)) pps
    in
    (impl_rels ps ((fun p -> P p), (fun p -> P p))) @ 
    (impl_rels ps ((fun p -> P p), (fun p -> NotP p))) @
    (impl_rels ps ((fun p -> NotP p), (fun p -> P p))) @
    (impl_rels ps ((fun p -> NotP p), (fun p -> NotP p)))
    
  let verify_antichain: predP list -> (string * string list) list -> (predP * predP) list = 
    fun ps vars -> 
    let impl_rels: predP list -> (predP * predP * int) list = 
      fun ps -> 
        (List.fold_right (fun p1 acc -> 
             List.fold_right (fun p2 acc' -> 
                 if p1 != p2 then (p1, p2)::acc'
                 else acc'
               ) ps acc) ps [])
        |> fun pps -> 
        let pred_rel p1 p2 = ELop (Smt.Or, [exp_of_predP (negate p1); exp_of_predP p2]) in
        let query_rel e = sp "(push 1)(assert (not %s))(check-sat)(pop 1)" (string_of_smt e) in
        let string_of_smt_query = unlines ~trailing_newline: true ([
            "(set-logic ALL)";
            string_of_smt_vars vars] @ 
            (List.map (fun (p1, p2) -> 
                 let e = pred_rel p1 p2 
                 in query_rel e
               ) pps)) 
        in
        pfvv "\nPRED RELS >>> \n%s\n" string_of_smt_query;
        flush stdout;
        let out = Provers.run_prover prover string_of_smt_query in
        if List.length out != (List.length pps) 
        then failwith "eval_predicates_rels";
        List.mapi(fun i (p1, p2) -> 
            let pp_sat_res = List.nth out i in
            if (pp_sat_res = "unsat") then (p1, p2, 0)
            else if (pp_sat_res = "sat") then (p1, p2, 1) 
            else (p1, p2, -1)) pps
    in
    let ps_partition = List.mapi (fun i p -> (i, p)) ps 
                     |> List.fold_left (fun acc (i, p) ->
                           match i mod 30, acc with  
                           | 0, _ -> [p]::acc
                           | _, [] -> [p]::acc
                           | _, pshd::pstl -> (p::pshd)::pstl
                         ) []
                     |> List.map impl_rels
                     |> List.flatten   
    in
    List.filter (fun (_, _, res) -> res = 0) ps_partition 
    |> List.map (fun (p1, p2, _) -> (p1, p2)) 

  let run_mc = 
    fun ps vars ->
    let count_summary = List.fold_left (fun acc p ->
        let p_mc = Model_counter.count_pred 
            "PREDICATE" 
            (string_of_smt_vars vars, string_of_smt @@  smt_of_pred p) in
        let not_p_mc = Model_counter.count_pred
            "PREDICATE"
            (string_of_smt_vars vars, string_of_smt @@ (EUop (Not, (smt_of_pred p))))
        in 
        (p,p_mc, not_p_mc) :: acc) [] ps
    in count_summary
    
end

let observe_rels = fun ps vars -> 
  let pred_rels = PredicateAnalyzer.observe_rels ps vars in
  let pred_orderings, pred_unknown_count, pred_unsolved  = List.fold_left (fun acc (p1, p2, res) -> 
      let (orderings, unknown_count, unsolved) = acc in
      if (res = 0) then ((p1, p2, res) :: orderings, unknown_count, unsolved)
      else if (res = 1) then (orderings, unknown_count + 1, unsolved)
      else (orderings, unknown_count, (p1, p2, res) :: unsolved)) ([], 0, []) pred_rels 
  in
  let module PAL = Predicate_analyzer_logger in
  PAL.log_predicates_impl_queries_result "Predicates IMPLICATION IMPLICATION QUERIES Summary" 
    pred_orderings pred_unknown_count pred_unsolved;
  pred_rels

let observe_rels_all = fun ps vars -> 
  let pred_all = List.fold_right (fun p acc -> (P p)::(NotP p)::acc) ps [] in
  let pred_rels = PredicateAnalyzer.observe_rels ps vars in
  let pred_rels_impl = List.fold_right (fun (p1, p2, res) acc -> 
      if (res = 0) then ((p1, p2)::acc)
      else acc) pred_rels []
  in
  let pred_rels_impl = 
    List.flatten @@ 
    (List.map (fun (p1, p2) -> [(p1, p2); (negate p2, negate p1)]) pred_rels_impl) 
  in
  let impl_antisymmetry (p1, p2) (pa, pb) = 
    (p1 = pb && p2 = pa)
  in
   let pred_eq = List.fold_right (fun pp1 acc ->
      List.fold_right (fun pp2 acc' ->
          if (impl_antisymmetry pp1 pp2) then pp1::acc'
          else acc'
        ) pred_rels_impl acc) pred_rels_impl []
  in
  let pred_equiv_classes: predP list -> (predP * predP) list -> predP list list = 
    fun ps pps ->
      let rec equiv_classes xs eqrels acc =
        match xs with
        | [] -> acc
        | x::xs' -> 
          let xeqrel = List.filter (fun (y1, y2) -> x = y1 || x = y2) eqrels in
          let xeqc = List.fold_right (
              fun (y1, y2) xyacc -> 
                let append_y = 
                  if (x = y1) then Some y2
                  else if (x = y2) then Some y1
                  else None 
                in
                match append_y with
                | Some y -> 
                  if (List.find_opt ((=) y) xyacc) = None then y::xyacc
                  else xyacc
                | None -> xyacc
            ) xeqrel [x]
          in
          let new_xs' = List.filter (fun x' -> (List.find_opt ((=) x') xeqc) = None) xs' in
          let new_xrels' = List.filter (fun (x', y') -> 
              (List.find_opt (fun x -> x = x' || x = y') xeqc) = None) eqrels
          in 
          equiv_classes new_xs' new_xrels' (xeqc::acc)
      in
      equiv_classes ps pps []
  in
  let pred_partition = pred_equiv_classes pred_all pred_eq in
  let pred_all', pred_rels_impl' = 
    List.fold_right (fun peqs (ps, pps) ->
        match peqs with
        | [] -> (ps, pps)
        | [p] -> (ps, pps)
        | p::ptl -> 
          ((List.filter (fun p' -> (List.find_opt ((=) p') ptl) = None) ps), 
           (List.filter (fun (p1', p2') -> 
                (List.find_opt ((=) p1') ptl) = None &&
                (List.find_opt ((=) p2') ptl) = None
              ) pps))
      ) pred_partition (pred_all, pred_rels_impl)
  in 
  let module PAL = Predicate_analyzer_logger in
  PAL.log_predicates_summary "Predicates Summary (initial list)" pred_all;
  PAL.log_predicates_impl_rels 
    "Predicates IMPLICATION REL Summary. Valid Implications" pred_rels_impl;
  PAL.log_predicates_equal_rels "Predicates EQUAL REL Summary. Valid Equalities" pred_eq;
  PAL.log_predicates_equiv_classes "Predicates EQUIVALENCE CLASSES Summary" pred_partition;
  PAL.log_predicates_summary "Predicates Summary (after filtering)" pred_all';
  PAL.log_predicates_impl_rels 
    "Predicates IMPLICATION REL Summary (after filtering). Valid Implications" pred_rels_impl';
  (pred_all', pred_rels_impl', pred_partition)
                          
let run_mc = fun ps vars ->
  let pred_mcs = PredicateAnalyzer.run_mc ps vars in
  let module PAL = Predicate_analyzer_logger in
  PAL.log_predicates_mc "Predicates MODEL COUNT Summary" ps pred_mcs;
  let pred_mcs_simplified = 
    List.flatten @@ (List.map (fun (p, p_mc, notp_mc) -> 
        match p_mc, notp_mc with
        | Sat v, Sat v' -> 
          let r = (float_of_int v) /. (float_of_int v') in 
          let delta_p = 0.5 *. (r -. 1.) /. (r +. 1.) in     (* delta_p    = 0.5*(v-v')/(v+v') *)
          let delta_notp = 0.5 *. (1. -. r) /. (r +. 1.) in  (* delta_notp = 0.5*(v'-v)/(v+v') *)
          [(P p, delta_p); (NotP p, delta_notp)]
        | ( Sat v, Unsat | Sat v, Unknown )  -> []
        | ( Unsat, _ | Unknown, _ ) -> []) pred_mcs ) 
  in
  pred_mcs_simplified
    
