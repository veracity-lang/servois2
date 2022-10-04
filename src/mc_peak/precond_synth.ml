open Util
open Lattice
open Smt
open Smt_parsing
open Provers
open Phi
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
     
let pfind: predP -> predP list list -> L.v L.el L.t -> L.v = 
  fun p pequivc l ->
  let ps' = List.find (fun ps -> List.mem p ps) pequivc in
  match List.fold_right (fun p res ->
      match res with
      | Some _ -> res
      | None -> L.find_opt (fun pr -> (fst pr) = p) l 
    ) ps' None with
  | Some pr -> pr
  | None -> raise @@ Failure (sp "Predicate %s not found" (string_of_predP p))
        
 
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
      if (x != y) then (p, y) :: acc 
      else acc
  ) ps (List.map2 (fun x y -> (x, y)) a b) []

(* choose the minimal object with the highest rank *)
let mcpeak = 
  fun l cmp cex_ncex ->
  let com, n_com = cex_ncex in
  let filtered_preds = List.map fst @@ differentiate_by_counterex l com n_com in
   pfv "\nFiltered predicates after differentiating: { %s }"
    (String.concat " ; " (List.map (fun a -> string_of_predP (fst a)) filtered_preds));
  let strongest_ps, _ = List.fold_right (fun p (sps, ps) ->
      if List.exists (fun p' -> p' != p && PO.lte p' p) ps then (sps, ps)
      else (p::sps, ps)) filtered_preds ([], filtered_preds)
  in
  (* match List.sort cmp strongest_ps with *)
  match List.sort cmp filtered_preds with
  | [] -> None
  | p::_ -> Some p  
  
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

  

