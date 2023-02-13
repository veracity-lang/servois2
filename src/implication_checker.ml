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
let rp2: rpred = (2, Gt, ["x"; "y"], ["z"])
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
(* x >= m *)
let rp10: rpred = (10, Gte, ["x"], ["m"])
(* x >= n *)
let rp11: rpred = (11, Gte, ["x"], ["n"])
(* x > m *)
let rp12: rpred = (12, Gt, ["x"], ["m"])
(* x > n *)
let rp13: rpred = (13, Gt, ["x"], ["n"])
(* x < m *)
let rp14: rpred = (14, Lt, ["x"], ["m"])
(* x < n *)
let rp15: rpred = (15, Lt, ["x"], ["n"])
(* x <= m *)
let rp16: rpred = (16, Lte, ["x"], ["m"])
(* x <= n *)
let rp17: rpred = (17, Lte, ["x"], ["n"])

(* list of predicates in premises or conclusions of rules *)
let rule_preds = [rp1; rp2; rp3; rp4; rp5; rp6; rp7; rp8; rp9; 
                  rp10; rp11; rp12; rp13; rp14; rp15; rp16; rp17 ]

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
  rp10, rp11, (function [m;n] -> m >= n | _ -> false);(* x >= m => x >= n, when m >= n *)
  rp12, rp13, (function [m;n] -> m >= n | _ -> false);(* x > m => x > n, when m >= n *)
  rp14, rp15, (function [m;n] -> m <= n | _ -> false);(* x < m => x < n, when m <= n *)
  rp16, rp17, (function [m;n] -> m <= n | _ -> false) (* x <= m => x <= n, when m <= n *)
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
      let tc = List.map (fun p -> (p, remove_self p @@ premises rs p [])) ps in
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
      (2, Gt, [x;y;z], _) -> if e2 = e4 then [(x, e1); (y, e3); (z, e2)] else []
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
    | (P (">=", e1, EConst e2_v), (10, Gte, [x], [m]) 
      | P (">=", e1, EConst e2_v), (11, Gte, [x], [m])) -> [(x, e1); (m, EConst e2_v)]
    | (P (">", e1, EConst e2_v), (12, Gte, [x], [m]) 
      | P (">", e1, EConst e2_v), (13, Gte, [x], [m])) -> [(x, e1); (m, EConst e2_v)]
    | (P ("<", e1, EConst e2_v), (14, Gte, [x], [m]) 
      | P ("<", e1, EConst e2_v), (15, Gte, [x], [m]))-> [(x, e1); (m, EConst e2_v)]
    | (P ("<=", e1, EConst e2_v), (16, Gte, [x], [m]) 
      | P ("<=", e1, EConst e2_v), (17, Gte, [x], [m]))-> [(x, e1); (m, EConst e2_v)]
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
          | [] -> true
          | bvar::tl -> 
            begin match List.assoc_opt bvar s, List.assoc_opt bvar s' with
              | Some x, Some x' -> if x = x' then agree_on_q_bvars s s' tl else false
              | _, _ -> false
            end
      in
      let rec collect_fterms s acc = function
        | [] -> acc
        | fvar::tl -> 
          match List.assoc_opt fvar s with
          | Some (EConst(CInt v)) -> collect_fterms s (v::acc) tl
          | _ -> collect_fterms s acc tl
      in 
      let fterms = collect_fterms s' (collect_fterms s [] (List.rev q_fvars)) (List.rev p_fvars) in
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
