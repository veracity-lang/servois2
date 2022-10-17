open Provers
open Model_counter
open Smt
open Smt_parsing
open Phi
open Spec
open Util

type 'a maybeRes = Exn of string | Val of 'a 

module type PredicateAnalyzerSig = 
sig
  val run_mc: spec -> method_spec -> method_spec -> pred list -> (predP * mc_result * mc_result) list
  val observe_rels: (module Prover) -> spec -> method_spec -> method_spec ->pred list -> (predP * predP * int) list
end

module PredicateAnalyzer: PredicateAnalyzerSig =
struct
 
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

  let vars_strings = curry3 @@ memoize @@ fun (spec, m1, m2) -> 
    let tybindings = spec.state @ m1.args @ m2.args in
    List.map (fun (v, t) -> sp "(declare-fun %s () %s)" (string_of_var v) (string_of_ty t)) 
      tybindings 
 
  let observe_rels = 
    fun (prover: (module Prover)) spec m1 m2 ps  -> 
    let module P = (val prover) in
    let impl_rels ps (liftp1, liftp2) = 
        pred_rel_set ps (liftp1, liftp2) 
        |> fun pps -> 
        let pred_rel p1 p2 = ELop (Smt.Or, [exp_of_predP (negate p1); exp_of_predP p2]) in
        let query_rel e = sp "(push 1)(assert (not %s))(check-sat)(pop 1)" (string_of_smt e) in
        let string_of_smt_query = unlines ~trailing_newline: true (
            ["(set-logic ALL);"] @
            begin match spec.preamble with
              | Some s -> [s]
              | None -> []
            end @ 
            (vars_strings spec m1 m2) @
            (List.map (fun (p1, p2) -> 
                 let e = pred_rel p1 p2 
                 in query_rel e
               ) pps)) 
        in
        pfvv "\nPRED RELS >>> \n%s\n" string_of_smt_query;
        flush stdout;
        let out = Provers.run_prover (module P) string_of_smt_query in
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

  let state_mc = curry3 @@ memoize (fun (spec, m1, m2) ->
      Model_counter.count_state spec m1 m2)
      
  let run_mc = 
    fun spec m1 m2 ps ->
    List.fold_left (fun acc p' ->
        let p = P p' in
        let p_mc = Model_counter.count_pred spec m1 m2 p in
        let not_p_mc = match p_mc, state_mc spec m1 m2 with
          | Sat x, Sat s -> Sat (s-x)
          | Sat _, stmc -> stmc
          | Unsat, stmc -> stmc
          | Unknown, stmc -> Unknown
        in 
        (p, p_mc, not_p_mc) :: acc) [] ps
end

let pequiv: predP list list -> predP -> predP -> bool = 
  fun pps p p' -> List.exists (fun ps -> List.mem p ps && List.mem p' ps) pps

let observe_rels (prover: (module Prover)) spec m1 m2 ps =
  let module PA = PredicateAnalyzer in
  let pred_all = List.fold_right (fun p acc -> (P p)::(NotP p)::acc) ps [] in
  let pred_rels = PA.observe_rels prover spec m1 m2 ps in
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
  let pred_eq = 
    let rec eqs all pps acc = 
      match pps with
      | [] -> acc
      | pp1::pps' ->
        if not @@ List.exists ((=) (snd pp1, fst pp1)) acc then begin
          if List.exists (impl_antisymmetry pp1) all then pp1::(eqs all pps' acc) 
          else (eqs all pps' acc) end
        else (eqs all pps' acc)
    in
    eqs pred_rels_impl pred_rels_impl []
  in

  let pred_equiv_classes: predP list -> (predP * predP) list -> predP list list = 
    fun ps pps ->
      let rec equiv_classes xs eqrels acc =
        match xs with
        | [] -> acc
        | x::xs' -> 
          let xeqrel = List.filter (fun (y1, y2) -> x = y1 || x = y2) eqrels in
          let xeqc = List.rev @@ List.fold_left (
              fun xyacc (y1, y2)-> 
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
            ) [x] xeqrel  
          in
          let new_xs' = List.filter (fun x' -> (List.find_opt ((=) x') xeqc) = None) xs' in
          let new_xrels' = List.filter (fun (x', y') -> 
              (List.find_opt (fun x -> x = x' || x = y') xeqc) = None) eqrels
          in 
          equiv_classes new_xs' new_xrels' (xeqc::acc)
      in
      List.rev @@ equiv_classes ps pps []
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
  PAL.log_predicates_equal_rels "Predicates EQUIV REL Summary. Valid Equivalences" pred_eq;
  PAL.log_predicates_equiv_classes "Predicates EQUIVALENCE CLASSES Summary" pred_partition;
  PAL.log_predicates_summary "Predicates Summary (after filtering)" pred_all';
  PAL.log_predicates_impl_rels 
    "Predicates IMPLICATION REL Summary (after filtering). Valid Implications" pred_rels_impl';
  (pred_all', pred_rels_impl', pred_partition)
                          
let run_mc = fun spec m1 m2 ps ->
  let module PA = PredicateAnalyzer in
  let pred_mcs = PA.run_mc spec m1 m2 ps in
  let module PAL = Predicate_analyzer_logger in
  PAL.log_predicates_mc "Predicates MODEL COUNT Summary" ps pred_mcs;
  let pred_mcs_simplified = 
    List.flatten @@ (List.map (fun (p, p_mc, notp_mc) -> 
        match p_mc, notp_mc with
        | Sat v, Sat v' -> 
          let r = (float_of_int v) /. (float_of_int v') in 
          let delta_p = 0.5 *. (r -. 1.) /. (r +. 1.) in     (* delta_p    = 0.5*(v-v')/(v+v') *)
          let delta_notp = 0.5 *. (1. -. r) /. (r +. 1.) in  (* delta_notp = 0.5*(v'-v)/(v+v') *)
          [(p, delta_p); (negate p, delta_notp)]
        | ( Sat v, Unsat | Sat v, Unknown )  -> []
        | ( Unsat, _ | Unknown, _ ) -> []) pred_mcs ) 
  in
  pred_mcs_simplified
    
let save_equivc outc pequivc = 
  Printf.fprintf outc "%s" 
    (String.concat "\n" 
       (List.map (fun ps -> String.concat "," @@ List.map string_of_predP ps) pequivc))

let load_equivc inc = 
  let rec add_c inc acc = 
    try
      let line = input_line inc in
      let predP_of_string s = 
        match predP_of_atom @@ exp_of_string s with
        | None -> raise @@ Failure (sp "Error parsing predicate %s" s)
        | Some p -> p
      in
      let ps = String.split_on_char ',' line |> List.map predP_of_string
      in add_c inc ([ps] @ acc)
    with End_of_file -> 
      acc
  in add_c inc []
       
