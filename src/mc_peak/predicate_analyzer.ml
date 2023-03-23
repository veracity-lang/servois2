open Provers
open Model_counter
open Smt
open Smt_parsing
open Phi
open Spec
open Util
open Solve

type 'a maybeRes = Exn of string | Val of 'a 

module type PredicateAnalyzerSig = 
sig
  val run_mc: spec -> method_spec -> method_spec -> pred list -> (predP * mc_result * mc_result) list
  val observe_rels: (module Prover) -> spec ->pred list -> (predP * predP * int) list
end

module VarSet = Set.Make (struct type t = string let compare = String.compare end)

module PredicateAnalyzer: PredicateAnalyzerSig =
struct
 
  let pred_rel_set: pred list -> (pred -> predP) * (pred -> predP) -> (predP * predP) list = 
    fun ps (liftp1, liftp2)->
      let vars p =  
        let rec vars_ e acc = 
          match e with
          | EVar ((Var _) as x) -> VarSet.union acc (VarSet.singleton (string_of_var x))
          | EVar ((VarM _) as x) -> VarSet.union acc (VarSet.singleton (string_of_var x))
          | EBop (_, e1, e2) -> vars_ e2 (vars_ e1 acc)
          | EUop (_, e1) -> vars_ e1 acc
          | ELop (_, es) -> List.fold_right vars_ es acc
          | EFunc (_, es) -> List.fold_right vars_ es acc
          | _ -> acc 
        in
        let _, e1, e2 = p in
        VarSet.union (vars_ e1 VarSet.empty) (vars_ e2 VarSet.empty)
      in
      let string_of_varset name vset = 
        sp "Vars (%s): {%s}" name (String.concat "," (List.of_seq (VarSet.to_seq vset)))
      in

      (* let ps = List.filteri (fun i p -> i < 30) ps in *)
      let pps_total, pps_excluded = ref 0, ref 0 in
      let aps = List.mapi (fun i p -> (i, p)) ps
      in aps 
         |> List.fold_left (
           fun acc (i, p) -> 
             (List.fold_left (
                 fun acc' (j, p') ->                 
                   if (i < j) then
                     begin
                       pps_total := !pps_total + 1;
                       (* filter out predicates with disjoint set of varoables *)
                       let vsetp, vsetp' = vars p, vars p' in
                       if (VarSet.disjoint vsetp vsetp') && 
                          (vsetp <> VarSet.empty || vsetp' <> VarSet.empty) then
                         begin
                           pps_excluded := !pps_excluded + 1;
                           pfv "Implication excluded %s => %s\n" 
                             (string_of_pred p) (string_of_pred p');
                           pfvv "VarsSet: %s , %s\n" 
                             (string_of_varset "p" vsetp) (string_of_varset "p'" vsetp');
                           acc
                         end
                       else
                         (liftp1 p, liftp2 p') :: acc'
                     end
                   else acc'
               ) acc aps)
         ) []
         |> (fun res ->
             pfv "Implication filtering summary: %d/%d" !pps_excluded !pps_total;
             res) 

  let observe_rels = 
    fun (prover: (module Prover)) spec ps  -> 
    let module P = (val prover) in
    let part_size = 300 in
    let rec partition: 'a list -> int -> int -> 'a list list -> 'b list list = 
      fun els psize i acc ->
        match els with
        | [] -> acc
        | el::tl when i < psize -> partition tl psize (i+1) ((el::(List.hd acc))::(List.tl acc))
        | el::tl when i = psize -> partition tl psize 1 ([el]::acc)
        | _ -> failwith "Unexpected pattern reached"
    in
    let impl_rels: pred list -> ((pred -> predP) * (pred -> predP)) -> (predP * predP * int) list = 
      fun ps (liftp1, liftp2) -> 
        pfv "\nLogical Implication Check\n";        
        pred_rel_set ps (liftp1, liftp2) 
        |> fun pps ->
        pfvv "\n# implications checked: %d\n" (List.length pps);
        (* I  => uncomment this to revert to the Logical Implication Checker *)
        (* let res = List.map (fun (p1, p2) -> 
         *     let conseq = Implication_checker.check_implication (p1, p2) in
         *     (p1, p2, if conseq then 0 else 1)
         *   ) pps 
         * in
         * let solv = List.length (List.filter (fun (_, _, flag_impl) -> flag_impl = 0) res) in   
         * pfv "\nLogical Implication: (=>) solved: %d/%d\n"
         *   (solv) (List.length pps);
         * res *)
  
        (* II. Run SMT Queries to discover all logical implications *)
        let pred_rel p1 p2 = ELop (Smt.Or, [exp_of_predP (negate p1); exp_of_predP p2]) in
        let query_rel e = sp "(push 1)(assert (not %s))(check-sat)(pop 1)" (string_of_smt e) in
       
        let string_of_smt_query pps_ = 
          unlines ~trailing_newline: true (
              [ "(set-logic ALL);"
              ; smt_of_spec spec] @
              (map_tr (fun (p1, p2) ->
                   let e = pred_rel p1 p2
                   in query_rel e
                 ) pps_))
        in
        partition pps part_size 0 [[]] 
        |> List.map (fun pps_ -> (string_of_smt_query pps_, pps_))
        |> List.map (fun (smt_query, pps_) ->
            pfvv "\nPRED RELS >>> \n%s\n" smt_query;
            pfvv "\nSMT Query string length: %d \n" (String.length smt_query);
            flush stdout;
            let out = Provers.run_prover (module P) smt_query in
            if List.length out != (List.length pps_) 
            then failwith "eval_predicates_rels";
            (List.mapi(fun i (p1, p2) ->
                 let pp_sat_res = List.nth out i in
                 if (pp_sat_res = "unsat") then (p1, p2, 0)
                 else if (pp_sat_res = "sat") then (p1, p2, 1)
                 else (p1, p2, -1)) pps_))
            |> List.flatten
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
          | Sat x, Sat s -> Sat (Z.sub s x)
          | Sat _, stmc -> stmc
          | Unsat, stmc -> stmc
          | Unknown, stmc -> Unknown
        in 
        (p, p_mc, not_p_mc) :: acc) [] ps
end

let pequiv: predP list list -> predP -> predP -> bool = 
  fun pps p p' -> List.exists (fun ps -> List.mem p ps && List.mem p' ps) pps

let observe_rels (prover: (module Prover)) spec ps =
  let module PA = PredicateAnalyzer in
  let pred_all = List.fold_right (fun p acc -> (P p)::(NotP p)::acc) ps [] in
  let pred_rels = PA.observe_rels prover spec ps in
  pfv "\n RELS solved\n";
  let rec pred_rels_impl_loop acc = function 
    | [] -> acc 
    | (p1, p2, 0)::tl -> pred_rels_impl_loop ((p1, p2)::acc) tl
    | hd::tl -> pred_rels_impl_loop acc tl
  in
  let pred_rels_impl = pred_rels_impl_loop [] pred_rels in
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
                  if not @@ List.exists ((=) y) xyacc then y::xyacc
                  else xyacc
                | None -> xyacc
            ) [x] xeqrel  
          in
          let new_xs' = List.filter (fun x' -> not @@ List.exists ((=) x') xeqc) xs' in
          let new_xrels' = List.filter (fun (x', y') -> 
              not @@ List.exists (fun x -> x = x' || x = y') xeqc) eqrels
          in 
          equiv_classes new_xs' new_xrels' (xeqc::acc)
      in
      equiv_classes ps pps [] |> List.map (List.sort (fun x y -> let f = compose size exp_of_predP in f x - f y)) |> List.rev
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
                          
let unknown_value = 0.0
let run_mc = fun spec m1 m2 ps ->
  let module PA = PredicateAnalyzer in
  let pred_mcs = PA.run_mc spec m1 m2 ps in
  let module PAL = Predicate_analyzer_logger in
  PAL.log_predicates_mc "Predicates MODEL COUNT Summary" ps pred_mcs;
  let pred_mcs_simplified = 
    List.flatten @@ (List.map (fun (p, p_mc, notp_mc) -> 
        match p_mc, notp_mc with
        | Sat v, Sat v' -> 
          let r = Q.to_float (Q.make v v') in 
          let delta_p = 0.5 *. (r -. 1.) /. (r +. 1.) in     (* delta_p    = 0.5*(v-v')/(v+v') *)
          let delta_notp = 0.5 *. (1. -. r) /. (r +. 1.) in  (* delta_notp = 0.5*(v'-v)/(v+v') *)
          [(p, delta_p); (negate p, delta_notp)]
        | ( Sat v, Unsat | Sat v, Unknown )  -> [(p, unknown_value); (negate p, unknown_value)]
        | ( Unsat, _ | Unknown, _ ) -> [(p, unknown_value); (negate p, unknown_value)]) pred_mcs ) 
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
