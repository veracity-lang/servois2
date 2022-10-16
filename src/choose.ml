open Smt
open Util
open Solve
open Provers
open Phi
open Spec
open Smt_parsing
open Lattice

let order_rels_set = ref []
module PO: ORDERED with type t = predP =
struct 
  type t = predP
  let lte = fun p1 p2 ->
    List.exists (fun (pa, pb) -> pa = p1 && pb = p2) !order_rels_set
  let string_of v = sp "%s" (string_of_predP v) 
end
module L = Lattice(PO)

type choose_env =
  { solver : (exp list -> exp -> solve_result)
  ; spec : spec
  ; m_spec: method_spec
  ; n_spec: method_spec
  ; h : conjunction
  ; choose_from : L.v L.el L.t
  ; choose_stronger_predicates: bool
  ; cex_ncex : bool list * bool list
  }

(* Assume that all predicate lists are sorted by complexity *)

let differentiating_predicates (ps : predP list) (a : bool list) b : ((predP * bool) list) = 
  (* The bool should be true if the predicate is true in the commute (first list) case *)
  (* TODO: Account for a/b not being simple true/false *)
  List.fold_right2 (fun p (x, y) acc -> if (x != y) then (p, y) :: acc else acc)
    ps (List.map2 (fun x y -> (x, y)) a b) []

let differentiating_predicates_sym (ps : predP list) (a : bool list) b : ((predP * bool) list) = 
  (* The bool should be true if the predicate is true in the commute (first list) case *)
  (* TODO: Account for a/b not being simple true/false *)
  List.fold_right2 (fun p (x, y) acc -> match p with | P _ -> if (x != y) then (p, y) :: acc else acc | _ -> acc) 
    ps (List.map2 (fun x y -> (x, y)) a b) []

let (* rec *) size = string_of_smt |> compose (String.split_on_char ' ') |> compose List.length
(* function
  | EVar _ -> 0
  | EArg _ -> raise @@ UnreachableFailure "Unbaked indexed argument"
  | EConst _ -> 0
  | EBop(_, e1, e2) -> 2 + size e1 + size e2
  | EUop(_, e) -> 1 + size e
  | ELop(_, es) -> List.length es + list_sum (List.map size es)
  | ELet(_, e) -> 1 + size e
  | EITE(e1, e2, e3) -> 3 + size e1 + size e2 + size e3
  | EFunc(_, es) -> List.length es + list_sum (List.map size es)
*)

let preds_of_lattice l = L.list_of l

let complexity : predP -> int = memoize @@ fun p -> match p with 
    | P (_, left, right) -> size left + size right
    | NotP (_, left, right) -> 1 + size left + size right

let simple env : predP =
    differentiating_predicates_sym (preds_of_lattice env.choose_from) (fst env.cex_ncex) (snd env.cex_ncex) |> List.hd |> fst

let poke env : predP =
    let com, n_com = env.cex_ncex in
    let next = differentiating_predicates_sym (preds_of_lattice env.choose_from) com n_com in
    let diff_preds = List.map fst next in
    let smt_diff_preds = List.map exp_of_predP diff_preds in
    let weight_fn p =
        let h'  = add_conjunct (exp_of_predP p) env.h in
        let h'' = add_conjunct (exp_of_predP @@ negate p) env.h in
        let weight_fn_inner h_com h_ncom = match env.solver smt_diff_preds @@ commute env.spec h_com with
            | Unsat -> 0
            | Unknown -> List.length smt_diff_preds
            | Sat vs -> begin let com_cex = pred_data_of_values vs in
                match env.solver smt_diff_preds @@ non_commute env.spec h_ncom with
                | Unsat -> 0
                | Unknown -> List.length smt_diff_preds
                | Sat vs -> begin let non_com_cex = pred_data_of_values vs in
                    differentiating_predicates_sym diff_preds com_cex non_com_cex |> List.length
                    end
                end in
        weight_fn_inner h' h' + weight_fn_inner h'' h'' in
    fst3 @@ match next with 
        | [] -> failwith "poke"
        | (p, b) :: next' -> List.fold_left (fun (p, weight, shortcircuit) (e, _) ->
        if shortcircuit then (p, weight, shortcircuit) else
        let e_weight = weight_fn e  in 
        if e_weight = -1 then (e, e_weight, true) else
        if e_weight < weight then (e, e_weight, false) else
        (p, weight, false)) (let weight = weight_fn p in (p, weight, weight = -1)) next'

let poke2 env : predP =
    let com, n_com = env.cex_ncex in
    let next = differentiating_predicates_sym (preds_of_lattice env.choose_from) com n_com in
    let diff_preds = List.map fst next in
    let smt_diff_preds = List.map exp_of_predP diff_preds in
    let weight_fn p cov =
        let h'  = add_conjunct (exp_of_predP @@ (if cov then Fun.id else negate) p) env.h in
        let h'' = add_conjunct (exp_of_predP @@ (if cov then negate else Fun.id) p) env.h in
        match env.solver smt_diff_preds @@ commute env.spec h' with
        | Unsat -> begin match env.solver smt_diff_preds @@ non_commute env.spec h'' with
            | Unsat -> -1
            | Unknown -> List.length smt_diff_preds
            | Sat s -> 0
            end
        | Unknown -> List.length smt_diff_preds (* Memoize for efficiency? Use max_int? *)
        | Sat vs -> begin let com_cex = pred_data_of_values vs in
            match env.solver smt_diff_preds @@ non_commute env.spec h'' with
            | Unsat -> 0
            | Unknown -> List.length smt_diff_preds
            | Sat vs -> begin let non_com_cex = pred_data_of_values vs in
                differentiating_predicates_sym diff_preds com_cex non_com_cex |> List.length
                end
            end in
    fst4 @@ match next with 
        | [] -> failwith "poke2"
        | (p, b) :: next' -> List.fold_left (fun (p, cov, weight, shortcircuit) (e, e_cov) ->
        if shortcircuit then (p, cov, weight, shortcircuit) else
        let e_weight = weight_fn e e_cov  in 
        if e_weight = -1 then (e, e_cov, e_weight, true) else
        if e_weight < weight then (e, e_cov, e_weight, false) else
        (p, cov, weight, false)) (let weight = weight_fn p b in (p, b, weight, weight = -1)) next'


let compare_pred_bisect p1 p2 = 
  let r1 = snd p1 in
  let r2 = snd p2 in 
  if (Float.abs r1) < (Float.abs r2) then -1
  else if (Float.abs r1) > (Float.abs r2) then 1
  else if r1 > r2 then -1
  else if r1 < r2 then 1
  else 0

let compare_pred_maximum_cover p1 p2 = 
  let r1 = snd p1 in
  let r2 = snd p2 in 
  if r1 > r2 then -1
  else if r1 < r2 then 1
  else 0
 
let pmcs_memo: (predP * float) list ref = ref []
let mc_run_time = ref 0.0
(* choose the minimal object with the highest rank *)
let mcpred env ps = 
  let pmcs_miss = List.filter (fun p -> not (List.exists (compose ((=) p) fst) !pmcs_memo)) ps in
  let pmcs = match pmcs_miss with
    | [] -> !pmcs_memo
    | pmcs_miss -> 
      let pmcs_miss' = List.fold_left (fun acc p -> 
          begin match p with
            | (P p' | NotP p') -> 
              begin match List.find_opt ((=) p') acc with None -> p'::acc | Some _ -> acc end
          end
        ) [] pmcs_miss in
      let start = Unix.gettimeofday () in
      let pmcs_ = Predicate_analyzer.run_mc env.spec env.m_spec env.n_spec pmcs_miss' in
      pmcs_memo := pmcs_ @ !pmcs_memo;
      mc_run_time := !mc_run_time +. ((Unix.gettimeofday ()) -. start);
      !pmcs_memo
  in
  List.map (fun p -> (p, List.assoc p pmcs)) ps 
        
let mcpeak cmp env =
  let l = env.choose_from in
  let cex_ncex = env.cex_ncex in 
  let com, n_com = cex_ncex in
  let filtered_preds = List.map fst @@ differentiating_predicates (preds_of_lattice l) com n_com 
                       |> mcpred env in
  pfv "\n[mcpeak] Filtered predicates after differentiating (before sorting): { %s }"
    (String.concat " ; " 
       (List.map (fun (p, r) -> sp "(%s, %.3f)" (predP_pretty_print p) r) filtered_preds));
  let filtered_preds = if env.choose_stronger_predicates then begin
  (* construct the subset with the strongest predicates amongst the candidates *)
      fst @@  List.fold_right (fun (p, r) (sps, ps) ->
          if List.exists (fun (p', r') -> p' != p && PO.lte p' p) ps then (sps, ps)
          else ((p, r)::sps, ps)) filtered_preds ([], filtered_preds) end 
    else
      filtered_preds
  in
      
  fst @@ list_min (fun x y -> cmp x y < 0) Fun.id filtered_preds


let mc_max : choose_env -> predP = mcpeak compare_pred_maximum_cover
let mc_bisect : choose_env -> predP = mcpeak compare_pred_bisect

let choose : (choose_env -> predP) ref = ref simple
