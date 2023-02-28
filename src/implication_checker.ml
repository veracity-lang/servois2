open Smt
open Util

type psymb = Gt | Gte | Lt | Lte | Eq | Neq                             (* predicate symbol     *)
type bvars = string list                                                (* bound variables      *)
type fvars = string list                                                (* free variables       *)
type rhypothesis = int list -> bool                                     (* rule hypothesis      *)
type substitution = (string * Smt.exp) list                             (* substitution         *)
type rpred = int * psymb * bvars * fvars                                (* predicate in rule    *)
type rules = (rpred * rpred * rhypothesis) list                         (* inference rule       *)

let empty_rhypothesis: rhypothesis = fun _ -> true

let string_of_psymb: psymb -> string = function
  | Gt -> "Gt" | Gte -> "Gte" | Lt -> "Lt" | Lte -> "Lte" | Eq -> "Eq" | Neq -> "Neq"
let string_of_rpred: rpred -> string = 
  fun (id, symb, bv, fv) ->
  Printf.sprintf "RPred: (%d, %s, [%s], [%s])" 
    id (string_of_psymb symb) (String.concat ";" bv) (String.concat ";" fv)
let string_of_substitution: substitution -> string = 
  fun s -> 
  Printf.sprintf "[%s]" @@ 
  String.concat " ; " (List.map (fun (x, e) -> Printf.sprintf "%s |-> %s" x (string_of_smt e)) s)

(* x > y *)
let rp1: rpred = (1, Gt, ["x"; "y"], []) 
(* x + z > y + z *)
let rp2: rpred = (2, Gt, ["x"; "y"], [])
(* x + m > y + n*)
let rp3: rpred = (3, Gt, ["x"; "y"], ["m"; "n"])        
(* x = y *)
let rp4: rpred = (4, Eq, ["x"; "y"], [])
(* x != y *)
let rp5: rpred = (5, Neq, ["x"; "y"], [])
(* x - y > 0 *)
let rp6: rpred = (6, Gt, ["x"; "y"], [])
(* x - y > n *)
let rp7: rpred = (7, Gt, ["x"; "y"], ["n"])
(* x > y + n *)
let rp8: rpred = (8, Gt, ["x"; "y"], ["n"])   
(* x - y = 0 *)
let rp9: rpred = (9, Eq, ["x"; "y"], [])
(* x >= n *)
let rp10: rpred = (10, Gte, ["x"], ["n"])
(* x > n *)
let rp12: rpred = (12, Gt, ["x"], ["n"])
(* x < n *)
let rp14: rpred = (14, Lt, ["x"], ["n"])
(* x <= n *)
let rp16: rpred = (16, Lte, ["x"], ["n"])
(* x + y > y | y + x > y*)
let rp18: rpred = (18, Gt, ["x"], [])
(* x > 0 *)
let rp19: rpred = (19, Gt, ["x"], [])
(* x - z > y - z *)
let rp20: rpred = (20, Gt, ["x"; "y"], [])
(* x + y = y | y + x = y *)
let rp21: rpred = (21, Eq, ["x"], [])
(* x = 0 *)
let rp22: rpred = (22, Eq, ["x"], [])

(* not (x > y) *)
let rp23: rpred = (23, Lte, ["x"; "y"], []) 
(* not (x + z > y + z) *)
let rp24: rpred = (24, Lte, ["x"; "y"], [])
(* not (x - y = 0) *)
let rp25: rpred = (25, Neq, ["x"; "y"], [])
(* not (x - y > n) *)
let rp26: rpred = (26, Lte, ["x"; "y"], ["n"])
(* not (x > y + n) *)
let rp27: rpred = (27, Lte, ["x"; "y"], ["n"]) 
(* not (x - z > y - z) *)
let rp28: rpred = (28, Lte, ["x"; "y"], [])
(* not (x + y > y) | not (y + x > y) *)
let rp29: rpred = (29, Lte, ["x"], [])
(* not (x > 0) *)
let rp30: rpred = (30, Lte, ["x"], [])
(* not (x + y = y) | not (y + x = y) *)
let rp31: rpred = (31, Neq, ["x"], [])
(* not (x = 0) *)
let rp32: rpred = (32, Neq, ["x"], [])

(* list of predicates in premises or conclusions of rules *)
let rule_preds = [rp1; rp2; rp3; rp4; rp5; rp6; rp7; rp8; rp9; 
                  rp10; rp12; rp14; rp16; rp18; rp19; rp20; rp21; rp22;
                  rp23; rp24; rp25; rp26; rp27; rp28; rp29; rp30; rp31; rp32 ]

(* rules are defined as ordered pairs of predicates + a hypothesis *)
let defined_rules: rules = [
  rp1, rp2, empty_rhypothesis;                       (* x > y   =>  x + z > y + z   *)
  rp2, rp1, empty_rhypothesis;                       (* x + z > y + z =>  x > y   *)
  rp1, rp6, empty_rhypothesis;                       (* x > y   =>  x - y > 0   *)
  rp6, rp1, empty_rhypothesis;                       (* x - y > 0   =>  x > y    *)
  rp1, rp3, (function [m;n] -> m >= n | _ -> false); (* x > y  =>  x + m > y + n, when m >= n *)
  rp1, rp5, empty_rhypothesis;                       (* x > y =>  x != y   *)
  rp7, rp8, empty_rhypothesis;                       (* x - y > n =>  x > y + n   *)
  rp8, rp7, empty_rhypothesis;                       (* x > y + n =>  x - y > n   *)
  rp3, rp1, (function [m;n] -> m <= n | _ -> false); (* x + m > y + n   =>  x > y, when m < n *)
  rp9, rp4, empty_rhypothesis;                       (* x - y = 0  =>  x = y   *)
  rp4, rp9, empty_rhypothesis;                       (* x = y  =>  x - y = 0   *)
  rp10, rp10, (function [n1;n2] -> n1 >= n2 | _ -> false);(* x >= n1 => x >= n2, when n1 >= n2 *)
  rp12, rp12, (function [n1;n2] -> n1 >= n2 | _ -> false);(* x > n1 => x > n2, when n1 >= n2 *)
  rp12, rp10, (function [n1;n2] -> n1 >= n2 | _ -> false);(* x > n1 => x >= n2, when n1 >= n2 *)
  rp14, rp14, (function [n1;n2] -> n1 <= n2 | _ -> false);(* x < n1 => x < n2, when n1 <= n2 *)
  rp16, rp16, (function [n1;n2] -> n1 <= n2 | _ -> false);(* x <= n1 => x <= n2, when n1 <= n2 *)
  rp14, rp16, (function [n1;n2] -> n1 <= n2 | _ -> false);(* x < n1 => x <= n2, when n1 <= n2 *)
  rp18, rp19, empty_rhypothesis;                     (* x + y > y => x > 0 *)
  rp19, rp18, empty_rhypothesis;                     (* x > 0 => x + y > y *)
  rp20, rp1, empty_rhypothesis;                      (* x - z > y - z  => x > y *)
  rp1, rp20, empty_rhypothesis;                      (* x > y => x - z > y - z *)
  rp21, rp22, empty_rhypothesis;                     (* x + y = y => x = 0 *)
  rp22, rp21, empty_rhypothesis;                     (* x = 0 => x + y = y *)
  
  rp23, rp24, empty_rhypothesis;                     (* not (x > y) => not (x + z > y + z) *)
  rp24, rp23, empty_rhypothesis;                     (* not (x + z > y + z) => not (x > y) *)
  rp25, rp5, empty_rhypothesis;                      (* not (x - y = 0) => not (x = y) *)
  rp5, rp25, empty_rhypothesis;                      (* not (x = y) => not (x - y = 0) *)
  rp26, rp27, empty_rhypothesis;                     (* not (x - y > n) => not (x > y + n) *)
  rp27, rp26, empty_rhypothesis;                     (* not (x > y + n) => not (x - y > n) *)
  rp23, rp28, empty_rhypothesis;                     (* not (x > y) => not (x - z > y - z) *)
  rp28, rp23, empty_rhypothesis;                     (* not (x - z > y - z) => not (x > y) *)
  rp29, rp30, empty_rhypothesis;                     (* not (x + y > y) => not (x > 0) *)
  rp30, rp29, empty_rhypothesis;                     (* not (x > 0) => not (x + y > y) *)
  rp31, rp32, empty_rhypothesis;                     (* not (x + y = y) => not (x = 0) *)
  rp32, rp31, empty_rhypothesis;                     (* not (x = 0) => not (x + y = y) *)
]

(* To compute the transitive closure of the implication relation under the set of 
*  predefined rules we perform a DFS traversal for each vertex in a graph representation of the
*  implication relation. Vertices and edges represent predicates and rules, respectively. 
*  Running time is V * (V + E) *)
let trans_clos: rpred list -> rules -> (rpred * (rpred * rhypothesis) list) list = 
  curry @@ memoize @@ (fun (ps, rs) -> 
      let rec remove_self p = function
        | [] -> []
        | (p', hyp)::tl -> if p == p' then tl else (p', hyp)::(remove_self p tl)
      in
      let rec premises: rules -> rpred -> (rpred * rhypothesis) list -> (rpred * rhypothesis) list = 
        fun rs p acc -> 
        add rs (List.find_all (fun (rpa, rpb, _) -> p == rpb) rs) acc 
      and add rs prms acc = 
        match prms with
        | (rpa, rpb, hypos)::tl ->
          if List.exists (fun (rp, hyp) -> rp == rpa) acc then add rs tl acc 
          else add rs tl (premises rs rpa ((rpa, hypos)::acc))
        | [] -> acc
      in
      let reflp p = List.find_all (fun (rpa, rpb, hyp) -> rpa == rpb && rpa == p) rs |> 
                          List.map (fun (rpa, _, hyp) -> (rpa, hyp)) in  
      let tc = List.map (fun p -> (p, (remove_self p @@ premises rs p []) @ (reflp p))) ps in
      pfvv "\n Transitive Closure: \n%s"
        (String.concat "\n" (List.map (fun (q, ps) -> 
             Printf.sprintf "(q: %s, premises: [%s])"
               (string_of_rpred q)
               (String.concat " ; " (List.map string_of_rpred (List.map fst ps)))) tc));
      tc
    )        

(* Algorithm that checks logical implication between two arbitrary predicates:
 * Key idea: 
 *   search for a rule that has a solution (general unifer) for the set of equations:
 *      p(e1, e2, ... e_n) = pr(bound_vars, free_vars) 
 *      q(e1', e2', ... e_n) = pr'(bound_vars, free_vars)
 *   and where the rule hypothesis holds.
 * Notation: 
 *   p, q    : ground instances of predicates
 *   pr, pr' : predicates defined in rules with bound and free variables. 
 *             The boundedness is with respect to the formula (p => q)      
 * ========                   
 * Input:
 *   pair (p, q) of predicates 
 * Output:
 *   true if p => q can be derived from the inference rules, false otherwise
 * Begin
 *   (1) find all conclusion predicates rp of the inference rules for which 
 *       exists a substitution s, s.t. rp(s) = q. 
 *   (2) repeat for each (rp, s)
 *       do
 *       - fix the bound variables in rp to the substituted terms in s
 *       - retrieve all possible premises of rp
 *   (3) - repeat for each prem = premise(rp)
 *         do
 *         - solve the equation p = prem, and find the substitution s'
 *         - if the substitutions s and s' agree on the bound terms of q 
 *            and the rule hypothesis holds, then return true
 *         od
 *       od
 *       return false     
 * End                        
 *)
let _check_implication: rpred list -> rules -> Smt.predP * Smt.predP -> bool = 
  fun rps rs (p,q) ->
  let fvarIdGen = ref 0 in
  let new_fvar m = fvarIdGen := !fvarIdGen + 1; m ^ (string_of_int !fvarIdGen) in
  let rec canonical_predP = function
    | P (">", EConst e1, e2) -> P ("<", e2, EConst e1)
    | P (">=", EConst e1, e2) -> P ("<=", e2, EConst e1)
    | P ("<", EConst e1, e2) -> P (">", e2, EConst e1)
    | P ("<=", EConst e1, e2) -> P (">=", e2, EConst e1)
    | P ("=", EConst e1, e2) -> P ("=", e2, EConst e1)
    | NotP (">", e1, e2) -> canonical_predP (P ("<=", e1, e2)) 
    | NotP (">=", e1, e2) -> canonical_predP (P ("<", e1, e2))
    | NotP ("<", e1, e2) -> canonical_predP (P (">=", e1, e2))
    | NotP ("<=", e1, e2) -> canonical_predP (P (">", e1, e2))
    | NotP ("=", EConst e1, e2) -> NotP ("=", e2, EConst e1)
    | p -> p
  in
  pfvv "\n Original p: %s, q: %s" (string_of_predP p) (string_of_predP q);
  let p, q = canonical_predP p, canonical_predP q in
  pfvv "\n Canonical p: %s, q: %s" (string_of_predP p) (string_of_predP q);
  let impl_clos = trans_clos rps rs in
  let unify_preds q rp = 
    pfvv "\nMatching Query: %s | %s" (string_of_predP q) (string_of_rpred rp);
    match q, rp with 
    | P (">", e1, e2), (1, Gt, [x;y], []) -> [(x, e1); (y, e2)]
    | P (">", ELop(Add, [e1; e2]), ELop(Add, [e3; e4])), 
      (2, Gt, [x;y], _) -> if e2 = e4 then [(x, e1); (y, e3)] else []
    | P (">", ELop(Add, [e1; (EConst(CInt e2_v)) as e2]), 
         ELop(Add, [e3; (EConst(CInt e4_v)) as e4])), 
      (3, Gt, [x;y], [m;n]) ->
      [(x, e1); (m, e2); (y, e3); (n, e4)]
    | P ("=", e1, e2), (4, Eq, [x;y], []) -> [(x, e1); (y, e2)]
    | NotP ("=", e1, e2), (5, Neq, [x;y], []) -> [(x, e1); (y, e2)]
    | P (">", EBop(Sub, e1, e2), EConst(CInt 0)), 
      (6, Gt, [x;y], _) ->
      [(x,e1); (y, e2)]
    | P (">", EBop(Sub, e1, e2), EConst e3), 
      (7, Gt, [x;y], [n]) ->
      [(x,e1); (y, e2); (n, EConst e3)]
    | P (">", e1, ELop(Add, [e2; EConst e3])), 
      (8, Gt, [x;y], [n]) ->
      [(x, e1); (y, e2); (n, EConst e3)]
    | P ("=", EBop(Sub, e1, e2), EConst(CInt 0)), (9, Eq, [x;y], []) -> [(x, e1); (y, e2)]
    | P (">=", e1, EConst e2_v), (10, Gte, [x], [m]) -> [(x, e1); (new_fvar m, EConst e2_v)]
    | P (">", e1, EConst e2_v), (12, Gt, [x], [m]) -> [(x, e1); (new_fvar m, EConst e2_v)]
    | P ("<", e1, EConst e2_v), (14, Lt, [x], [m]) -> [(x, e1); (new_fvar m, EConst e2_v)]
    | P ("<=", e1, EConst e2_v), (16, Lte, [x], [m]) -> [(x, e1); (new_fvar m, EConst e2_v)]
    | (P (">", ELop(Add, [e1; e2]), e3), (18, Gt, [x], [])) -> 
      if e1 = e3 then [(x, e2)] else if e2 = e3 then [(x, e1)] else []
    | (P (">", e1, EConst(CInt 0)), (19, Gt, [x], [])) -> [(x, e1)]
    | (P (">", EBop(Sub, e1, e2), EBop(Sub, e3, e4)), (20, Gt, [x;y], [])) ->
       if e2 = e4 then [(x, e1); (y, e3)] else []
    | (P ("=", ELop(Add, [e1; e2]), e3), (21, Eq, [x], [])) -> 
      if e1 = e3 then [(x, e2)] else if e2 = e3 then [(x, e1)] else []
    | (P ("=", e1, EConst(CInt 0)), (22, Eq, [x], [])) -> [(x, e1)]           
    | P ("<=", e1, e2), (23, Lte, [x;y], []) -> [(x, e1); (y, e2)]
    | P ("<=", ELop(Add, [e1; e2]), ELop(Add, [e3; e4])), (24, Lte, [x;y], _) -> 
      if e2 = e4 then [(x, e1); (y, e3)] else []
    | NotP ("=", EBop(Sub, e1, e2), EConst(CInt 0)), (25, Neq, [x; y], []) -> 
      [(x, e1); (y, e2)]
    | P ("<=", EBop(Sub, e1, e2), EConst e3), (26, Lte, [x;y], []) -> 
      [(x, e1); (y, e2)]
    | P ("<=", e1, ELop(Add, [e2; EConst e3])), (27, Lte, [x;y], []) -> 
      [(x, e1); (y, e2)]
    | P ("<=", EBop(Sub, e1, e2), EBop(Sub, e3, e4)), (28, Lte, [x;y], []) -> 
      if e2 = e4 then [(x, e1); (y, e3)] else []
    | P ("<=", ELop(Add, [e1; e2]), e3), (29, Lte, [x], []) -> 
      if e1 = e3 then [(x, e2)] else if e2 = e3 then [(x, e1)] else []
    | P ("<=", e1, EConst(CInt 0)), (30, Lte, [x], []) -> [(x, e1)]
    | NotP ("=", ELop(Add, [e1; e2]), e3), (31, Eq, [x], []) -> 
      if e1 = e3 then [(x, e2)] else if e2 = e3 then [(x, e1)] else []
    | NotP ("=", e1, EConst(CInt 0)), (32, Eq, [x], []) -> [(x, e1)]
                                                            
    | q, rp -> pfvv "\nUnmatched: %s | %s" (string_of_predP q) (string_of_rpred rp); []
  in
  let rec check_prms rp_q s = function
    [] -> false
    | (rp, hypos)::tl ->
      let (_, _, _, p_fvars) = rp in
      pfvv "\nCheck_Premises. Rpred(q): %s" (string_of_rpred rp_q);
      pfvv "\nCheck_Premises. Substitution s(q): %s" (string_of_substitution s);
      pfvv "\nCheck_Premises. Rpred(p): %s" (string_of_rpred rp);
      let s' = unify_preds p rp in
      pfvv "\nCheck_Premises. Substitution s'(p): %s" (string_of_substitution s');
      let _, _, q_bvars, q_fvars =  rp_q in
      let rec agree_on_q_bvars: substitution -> substitution -> string list -> bool = 
        fun s s' bvars ->
          match bvars with
          | [] -> pfvv "\nBvars agreement"; true
          | bvar::tl -> 
            begin match List.assoc_opt bvar s, List.assoc_opt bvar s' with
              | Some x, Some x' -> if x = x' then let () = pfvv "\nAgree on bvar" in agree_on_q_bvars s s' tl else false
              | _, _ -> false
            end
      in
      let rec collect_fterms s acc = function
        | [] -> acc
        | fvar::tl -> 
          pfvv "\nFVar: %s" fvar;
          match List.find_opt (fun (m, _) -> (String.sub m 0 (String.length fvar)) = fvar) s with
          | Some (fvar_m, EConst(CInt v)) -> 
            pfvv "\nFVar %s -> %d" fvar_m v; collect_fterms s (v::acc) tl
          | _ -> collect_fterms s acc tl
      in 
      let fterms = collect_fterms s' (collect_fterms s [] (List.rev q_fvars)) (List.rev p_fvars) in
      pfvv "\nFreeVar Terms: %s" (String.concat "; " (List.map string_of_int fterms));
      let rhypos_holds = hypos fterms in 
      if (agree_on_q_bvars s s' q_bvars) && rhypos_holds then true else check_prms rp_q s tl
      
  in
  let rec check rps result = 
    match result, rps with
    | (Some _, _ | None, []) -> result
    | None, rp::tl -> 
      begin match unify_preds q rp with
        | [] -> check tl result
        | s -> 
          pfvv "\nIMPL_CHECK: Conclusion Pred Match \n***\nq: %s \nrp: %s \ns: %s\n***" 
            (string_of_predP q)
            (string_of_rpred rp)
            (string_of_substitution s);
          begin match List.assoc_opt rp impl_clos with
            | None -> check tl result
            | Some prms -> if check_prms rp s prms then Some true else check tl result
          end
      end
  in
  pfvv "\nCheck implication %s => %s. Result = ?" (string_of_predP p) (string_of_predP q);
  let r = match check rps None with None -> false | Some r -> r in
  pfv "\nCheck implication %s => %s. Result = %b" (string_of_predP p) (string_of_predP q) r;
  r

let check_implication = _check_implication rule_preds defined_rules
