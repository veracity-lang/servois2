open Util
open Smt
open Lattice
open Model_counter

let string_of_pred ?(negate = false) ?(paran = ("", "")) (op, e1, e2) = 
    let open Smt.To_String in
    let op_pretty_print ?(negate = false) o = 
      match negate, o  with
      ( _, "+" | _, "-" | _, "*" | _, "div" | _, "mod" | _, "abs") -> o 
      | false, o -> o 
      | true, "=" -> "\u{2260}"
      | true, ">" -> "\u{2264}"
      | true, ">=" -> "<"
      | true, "<" -> "\u{2265}"
      | true, "<=" -> ">"
      | true, o -> sp "not %s" o 
    in
    let rec exp_pretty_print ?(negate = false) e = 
      match e with
      |EBop (o, e1, e2) -> sp "(%s %s %s)" 
                             (exp_pretty_print ~negate:negate e1) 
                             (op_pretty_print ~negate:negate (To_String.bop o))
                             (exp_pretty_print ~negate:negate e2)
      |ELop (Add as o, [e1; e2]) -> sp "(%s %s %s)" 
                             (exp_pretty_print ~negate:negate e1) 
                             (op_pretty_print ~negate:negate (To_String.lop o))
                             (exp_pretty_print ~negate:negate e2)
      |EFunc (f, es) -> 
        begin match f, es with
        | ("+", [e1;e2] | "-", [e1;e2] 
          | "*", [e1;e2] | "div", [e1;e2] 
          | "mod", [e1;e2]
          | "abs", [e1;e2]) ->
           sp ("%s %s %s") 
             (exp_pretty_print ~negate:negate e1) 
             (op_pretty_print ~negate:false f)
             (exp_pretty_print ~negate:negate e2)
        | _, _ -> To_String.exp e
        end
      | _ -> To_String.exp e
    in
    let e1_pp = exp_pretty_print ~negate:negate e1 in
    let e2_pp = exp_pretty_print ~negate:negate e2 in
    let op_pp = op_pretty_print ~negate:negate op in
    sp "%s%s %s %s%s" (fst paran) e1_pp op_pp e2_pp (snd paran)

let string_of_predP = function
  | P p -> string_of_pred ~paran:("(", ")") p
  | NotP p -> string_of_pred ~negate: true ~paran:("(", ")") p

let log_predicates_summary = 
  fun title pred_all -> 
  Printf.printf ("\n\n%s [%d]: \n%s\n") title
    (List.length pred_all)
    (String.concat "\n" (List.map (string_of_predP) pred_all))

let log_predicates_impl_rels = 
  fun title rels -> 
  Printf.printf ("\n\n%s [%d]: \n%s\n") title
    (List.length rels)
    (String.concat "\n" (List.map (fun (p1, p2) -> 
         (string_of_predP p1) ^ " => " ^
         (string_of_predP p2)) rels))

let log_predicates_impl_queries_result = 
  fun title impls unknown_count unsolved ->
  Printf.printf "\n\n%s Valid Implications [%d]: \n%s\n\n Unknown[%d]\n\nUnsolved[%d]: \n%s" title
    (List.length impls)
    (String.concat "\n" (List.map (fun (p1, p2, _) -> 
         (string_of_predP p1) ^ " => " ^
         (string_of_predP p2)) impls))
    unknown_count
    (List.length unsolved)
    (String.concat "\n" (List.map (fun (p1, p2, _) -> 
         (string_of_predP p1) ^ " => " ^
         (string_of_predP p2)) unsolved))

let log_predicates_equal_rels = 
  fun title rels -> 
  Printf.printf ("\n\n%s [%d]: \n%s\n") title
    (List.length rels)
    (String.concat "\n" (List.map (fun (p1, p2) -> 
         (string_of_predP p1) ^ " = " ^
         (string_of_predP p2)) rels))

let log_predicates_equiv_classes = 
  fun title partition -> 
  Printf.printf ("\n\n%s [%d]: \n%s\n") title
    (List.length partition)
    (String.concat "\n" (List.map (
         fun (ps) -> sp "{%s}" 
             (String.concat " ; " (List.map (string_of_predP) ps))) 
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
    |> List.sort (fun (_, _, _, v1) (_, _, _, v2) -> 
        if (v1 > v2) then 1
        else if (v1 == v2) then 0 
        else -1)
  in
  Printf.printf ("\n\n%s [%d]: \n%s") title
    (List.length ps)
    (String.concat "\n" (List.map (fun (p, p_mc, notp_mc, split_ratio) ->
       match p_mc, notp_mc with
       | Sat v, Sat v' ->
         let str_of_split_ratio r = 
           let a, b = r /. (r +. 1.), 1. /. (r +. 1.) in 
           sp "%.2f%% : %.2f%%" (a *. 100.) (b *. 100.)
         in
         sp "%-30s %-17i    | %-30s %-17i | split ratio [%s]" 
                            (string_of_pred p) v
                            (string_of_pred p ~negate:true) v'
                            (str_of_split_ratio split_ratio)
       | Sat v, Unsat -> sp "BUG: %-30s %-17i | not ~ [unsat]" (string_of_pred p) v
       | Sat v, Unknown -> sp "BUG: %-30s %-17i | not ~ [__unknown]" (string_of_pred p) v
       | Unsat, _ -> sp "%-30s [unsat]" (string_of_pred p)
       | Unknown, _ -> sp "%-30s [__unknown__]" (string_of_pred p)) ps_mc_sorted))


let log_ppeak_result = 
  fun (p, d) ps -> 
  Printf.printf "\nPPEAK RESULT: \nPredicate selected: %s\nPredicates remaining [%d]"
    (string_of_predP p) 
    (List.length ps)

let log_predicate_implication_chains : predP list -> (predP * predP) list -> unit =
  fun ps prels ->
  let module PO: ORDERED with type t = predP =
    struct 
      type t = predP 
      let lte = fun p1 p2 ->
        List.exists (fun (pa, pb) -> pa = p1 && pb = p2) prels
      let string_of = string_of_predP
    end 
  in
  let module L = Lattice(PO) in
  let l = L.construct ps in
  pfv "\n\nLATTICE.\n %s" (L.string_of l);
  let cs = L.chains_of l in
  Printf.printf "\n\nIMPLICATION CHAINS [%d]: \n%s\n\n"
    (List.length cs)
    (String.concat "\n" (List.map (
        fun pc -> String.concat " => " (
            List.map (string_of_predP) pc)) cs))
