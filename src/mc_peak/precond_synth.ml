open Util
open Lattice
open Smt
open Smt_parsing
open Provers
open Phi
open Choose
open Predicate_analyzer

module PAL = Predicate_analyzer_logger

type synth_options = {
  prover: (module Prover);
  timeout: float option;
  maximize_coverage: bool
}

let default_synth_options = {  
  prover = (module Provers.ProverCVC4);  
  timeout = None;
  maximize_coverage = false
}
 
let order_rels_set = ref []
module PO: ORDERED with type t = (predP * float) =
struct 
  type t = predP * float
  let lte = fun p1 p2 ->
    List.exists (fun (pa, pb) -> pa = fst p1 && pb = fst p2) !order_rels_set
  let string_of v = sp "%s [%.2f]" (PAL.string_of_predP @@ fst v) (snd v) 
end
module L = Lattice(PO)

let pequiv: predP list list -> predP -> predP -> bool = 
  fun pps p p' -> List.exists (fun ps -> List.mem p ps && List.mem p' ps) pps
      
let compare_pred_bisect p1 p2 = 
  let r1 = snd p1 in
  let r2 = snd p2 in 
  if (Float.abs r1) < (Float.abs r2) then -1
  else if (Float.abs r1) > (Float.abs r2) then 1
  else 0

let compare_pred_maximum_cover p1 p2 = 
  let r1 = snd p1 in
  let r2 = snd p2 in 
  if r1 > r2 then -1
  else if r1 < r2 then 1
  else 0
 
let differentiate_by_counterex = 
  fun l a b ->
  let ps = L.list_of l in 
  List.fold_right2 (
    fun p (x, y) acc ->
      (* only predicates that hold *)
      if (x != y) then (p, y) :: acc 
      else acc
  ) ps (List.map2 (fun x y -> (x, y)) a b) []

let gen_next_candidates = 
  fun l cmp cex_ncex -> 
  let com, n_com = cex_ncex in
  let filtered_preds = List.map fst @@ differentiate_by_counterex l com n_com in
   pfv "\nFiltered predicates after differentiating: { %s }"
    (String.concat " ; " (List.map (fun a -> string_of_predP (fst a)) filtered_preds));
  let strongest_ps, weaker_ps, _ = List.fold_left (fun (sps, wps, ps) p ->
      if List.exists (fun p' -> p' != p && PO.lte p' p) ps then (sps, p::wps, ps)
      else (p::sps, wps, ps)) ([], [], filtered_preds) filtered_preds
  in
  let l_ps = L.list_of l in
  (List.sort cmp @@ List.filter (fun p -> List.exists (fun p' -> p = p') strongest_ps) l_ps) @ 
  (List.sort cmp @@ List.filter (fun p -> List.exists (fun p' -> p = p') weaker_ps) l_ps)
  
let construct_lattice = 
  fun psmcs pps ->
  order_rels_set := pps;
  let l = L.construct psmcs in
  pfv "\n\nLATTICE:\n%s" (L.string_of l);
  l

let print_pred_candidates cs = 
  pfv "\n\nCandidates ordered [%d]: { %s }\n"
    (List.length cs)
    (String.concat " ; " (List.map (PO.string_of) cs))

  

