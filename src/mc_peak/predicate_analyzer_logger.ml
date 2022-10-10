open Util
open Smt
open Lattice
open Model_counter

let log_predicates_summary = 
  fun title pred_all -> 
  pfv ("\n\n%s [%d]: \n%s\n") title
    (List.length pred_all)
    (String.concat "\n" (List.map (string_of_predP) pred_all))

let log_predicates_impl_rels = 
  fun title rels -> 
  pfv ("\n\n%s [%d]: \n%s\n") title
    (List.length rels)
    (String.concat "\n" (List.map (fun (p1, p2) -> 
         (predP_pretty_print p1) ^ " => " ^
         (predP_pretty_print p2)) rels))

let log_predicates_impl_queries_result = 
  fun title impls unknown_count unsolved ->
  pfv "\n\n%s Valid Implications [%d]: \n%s\n\n Unknown[%d]\n\nUnsolved[%d]: \n%s" title
    (List.length impls)
    (String.concat "\n" (List.map (fun (p1, p2, _) -> 
         (predP_pretty_print p1) ^ " => " ^
         (predP_pretty_print p2)) impls))
    unknown_count
    (List.length unsolved)
    (String.concat "\n" (List.map (fun (p1, p2, _) -> 
         (predP_pretty_print p1) ^ " => " ^
         (predP_pretty_print p2)) unsolved))

let log_predicates_equal_rels = 
  fun title rels -> 
  pfv ("\n\n%s [%d]: \n%s\n") title
    (List.length rels)
    (String.concat "\n" (List.map (fun (p1, p2) -> 
         (predP_pretty_print p1) ^ " = " ^
         (predP_pretty_print p2)) rels))

let log_predicates_equiv_classes = 
  fun title partition -> 
  pfv ("\n\n%s [%d]: \n%s\n") title
    (List.length partition)
    (String.concat "\n" (List.map (
         fun (ps) -> sp "{%s}" 
             (String.concat " ; " (List.map (predP_pretty_print) ps))) 
         partition))

let log_predicates_mc = 
  fun title ps ps_mc->
  let ps_mc_sorted = 
    List.map (fun (p, p_mc, notp_mc) -> 
        match p_mc, notp_mc with
        | Sat v, Sat v' -> 
           (p, p_mc, notp_mc, (float_of_int v) /. (float_of_int v'))
        | _, _ -> (p, p_mc, notp_mc, -1.)
      ) ps_mc 
    |> List.stable_sort (fun (_, _, _, v1) (_, _, _, v2) -> 
        if (v1 > v2) then 1
        else if (v1 == v2) then 0 
        else -1)
  in
  pfv ("\n\n%s [%d]: \n%s") title
    (List.length ps)
    (String.concat "\n" (List.map (fun (p, p_mc, notp_mc, split_ratio) ->
       match p_mc, notp_mc with
       | Sat v, Sat v' ->
         let str_of_split_ratio r = 
           let a, b = r /. (r +. 1.), 1. /. (r +. 1.) in 
           sp "%.2f%% : %.2f%%" (a *. 100.) (b *. 100.)
         in
         sp "%-30s %-17i    | %-30s %-17i | split ratio [%s]" 
                            (predP_pretty_print p) v
                            (predP_pretty_print (negate p)) v'
                            (str_of_split_ratio split_ratio)
       | Sat v, Unsat -> sp "BUG: %-30s %-17i | not ~ [unsat]" (predP_pretty_print p) v
       | Sat v, Unknown -> sp "BUG: %-30s %-17i | not ~ [__unknown]" (predP_pretty_print p) v
       | Unsat, _ -> sp "%-30s [unsat]" (predP_pretty_print p)
       | Unknown, _ -> sp "%-30s [__unknown__]" (predP_pretty_print p)) ps_mc_sorted))


let log_ppeak_result = 
  fun (p, d) ps -> 
  pfv "\nPPEAK RESULT: \nPredicate selected: %s\nPredicates remaining [%d]"
    (predP_pretty_print p) 
    (List.length ps)

let log_predicate_implication_chains : predP list -> (predP * predP) list -> unit =
  fun ps prels ->
  let module PO: ORDERED with type t = predP =
    struct 
      type t = predP 
      let lte = fun p1 p2 ->
        List.exists (fun (pa, pb) -> pa = p1 && pb = p2) prels
      let string_of = predP_pretty_print
    end 
  in
  let module L = Lattice(PO) in
  let l = L.construct ps in
  pfv "\n\nLATTICE.\n %s" (L.string_of l);
  let cs = L.chains_of l in
  pfv "\n\nIMPLICATION CHAINS [%d]: \n%s\n\n"
    (List.length cs)
    (String.concat "\n" (List.map (
        fun pc -> String.concat " => " (
            List.map (predP_pretty_print) pc)) cs))

let print_pred_candidates cs = 
  pfv "\n\nCandidates ordered [%d]: { %s }\n"
    (List.length cs)
    (String.concat " ; " (List.map (predP_pretty_print) cs))
