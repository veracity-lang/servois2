open Smt
open Spec
open Phi
open Util
open Solve

type mc_result = 
  | Sat of Z.t
  | Unsat
  | Unknown

let n_queries = ref 0

type smt_mc_formulae = string * string * string * string * string
type region_predicate = HPredConj of conjunction | HPredDisj of disjunction

(* Model counter interface, e.g. ABC MC *)
module type ModelCounterSig = sig
  val name : string
  val exec_paths : string list
  val bound_int : int
  val smt_fname : string
  val args : string array
  val parse_output : string list * string list -> mc_result
end

(* Interface for counting regions of satisfying models where 
   conditions hold for ADT's commuting operations *)
module type PredicateModelCountSig = 
sig
  val count_state: spec -> method_spec -> method_spec -> mc_result
  val count_pred: spec -> method_spec -> method_spec -> predP -> mc_result
  val count_conj: spec -> method_spec -> method_spec -> conjunction -> mc_result
end

module ABCModelCounter : ModelCounterSig = 
struct
  let name = "abc"

  let exec_paths = [    
    "/usr/local/bin/abc";
    "/usr/bin/abc"
  ]
  
  let smt_fname = "tmp.smt2"

  let bound_int = 4
  let bound_str = 4

  let args = [| ""; "-v"; "0"; 
                "-bi"; string_of_int bound_int; 
                "-bs"; string_of_int bound_str; 
                "-i"; smt_fname |]

  let line_count_regex = Str.regexp {|.*report bound: [0-9]+ count: \([0-9]+\) time:.*.*|}

  let rec parse_mc_report ls = 
    match ls with
    | [] -> Unknown
    | l::ls' ->
       if Str.string_match line_count_regex l 0 then begin
         try Sat (Z.of_string @@ Str.matched_group 1 l) with e -> 
           let msg = Printexc.to_string e
           and stack = Printexc.get_backtrace () in
           pfvv "\nError when converting MC result: \nmsg:%s\nstack:%s\n" msg stack;
           Unknown
       end
       else parse_mc_report ls'

  
    
  let parse_sat (sout, serr) = 
    match sout, serr with
    | [], [] -> Unknown
    | l::ls, _ -> begin try Sat (Z.of_string l) with e ->
        let msg = Printexc.to_string e
        and stack = Printexc.get_backtrace () in
        pfvv "\nError when converting MC result: \nmsg:%s\nstack:%s\n" msg stack;
        Unknown
      end
    | [], rls -> parse_mc_report rls 

  let rec parse_output = function (sout, serr) ->  
    match sout with
    | [] -> Unknown
    | l::ls ->
      if (String.equal l "sat") then parse_sat (ls, serr)  
      else if (String.equal l "unsat") then Unsat else parse_output (ls, serr) 
   
  (* 
    if Str.string_match line_count_regex l 0 then begin
         let matched_val = Str.matched_group 1 l in
         pfvv "\nMatched value: %s" matched_val;
         let mc = try int_of_string matched_val with e ->
            let msg = Printexc.to_string e
            and stack = Printexc.get_backtrace () in
            pfvv "\nError when converting result: \nmsg:%s\nstack:%s\n" msg stack; raise e
         in
         (* Sat (int_of_string @@ Str.matched_group 1 l) *)
         Sat mc
         end
       else parse_mc_report ls'
  *)

end  

let run_mc_exec (prog : string) (args : string array) (smt_fname : string) =
  let chan_out, chan_in, chan_err =
    Unix.open_process_args_full prog args [||] in
  let pid = Unix.process_full_pid (chan_out, chan_in, chan_err) in
  Sys.set_signal Sys.sigalrm (
      Sys.Signal_handle (fun _ ->
          Unix.kill pid Sys.sigkill;
          raise Timeout)
      );
  flush stdout;
  let _ = waitpid_poll pid in
  set_timeout_handler ();
  let sout = read_all_in chan_out in
  let serr = read_all_in chan_err in
  close_out chan_in;
  sout, serr

let print_exec_result (out : string list) (err : string list) =
  pfvv "* * * OUT * * * \n%s\n* * * ERR * * * \n%s\n* * * * * *\n"
    (String.concat "\n" out) (String.concat "\n" err)

let run_model_counter (counter : (module ModelCounterSig)) =
    let module MC = (val counter) in
    let exec = find_exec MC.name MC.exec_paths in
    let sout, serr = run_mc_exec exec MC.args MC.smt_fname in
    print_exec_result sout serr;
    n_queries := !n_queries + 1;
    sout, serr

module PredicateModelCount: PredicateModelCountSig = 
struct        
  let create_smt_file smt fname = 
    let oc = open_out fname in
    Printf.fprintf oc "%s" smt;
    close_out oc

  let remove_smt_file fname = 
    Sys.remove fname

  let run_mc mc_query = 
    let module MC = ABCModelCounter in
    pfvv "\nModel counter query: \n%s\n" mc_query;
    create_smt_file mc_query MC.smt_fname;
    let result = run_model_counter (module MC) |> MC.parse_output in
    pfvv "\nModel counter result: \n%s\n--------------------------\n" 
      (begin match result with
         | Sat c -> sp "Sat; bound %d; count: %s" MC.bound_int (Z.to_string c)
         | Unsat -> "Unsat"
         | Unknown -> "Unknown"
       end);
    remove_smt_file MC.smt_fname;
    result  

  let rec repl_compound_index_terms: ty bindlist -> (unit -> exp) -> exp -> exp * (exp list) = 
    fun fva freshvar_gen e -> 
    match e with
    | (EVar _ | EArg _ | EConst _ ) -> (e, [])
    | EBop(b, el, er) -> 
      let el', newcl = repl_compound_index_terms fva freshvar_gen el in  
      let er', newcr = repl_compound_index_terms fva freshvar_gen er in
      (EBop(b, el', er'), newcl @ newcr)
    | EUop(u, e) -> 
      let e', newc = repl_compound_index_terms fva freshvar_gen e in
      (EUop(u, e'), newc)  
    | ELop(lop, es) -> 
      let es', newcs = List.split @@ List.map (repl_compound_index_terms fva freshvar_gen) es in
      (ELop(lop, es'), List.flatten newcs)   
    | (ELet(_, _) | EExists(_, _)) -> (e, [])  
    | EITE(g, tb, fb) ->
      let g', newcg = repl_compound_index_terms fva freshvar_gen g in
      let tb', newct = repl_compound_index_terms fva freshvar_gen tb in
      let fb', newcf = repl_compound_index_terms fva freshvar_gen fb in
      (EITE(g', tb', fb'), newcg @ newct @ newcf)
    | EFunc("select", [EVar a; ei]) -> 
      begin match List.assoc_opt a fva with
        | Some _ ->   
          begin match ei with
            | (EVar _ | EArg _ | EConst _ ) -> (e, [])
            | ELop _ -> (e, [])
            | _ -> 
              let i_new = freshvar_gen () in
              (EFunc("select", [EVar a; i_new]), [ELop(And, [i_new; ei])])
          end
        | None -> 
          let i', newci = repl_compound_index_terms fva freshvar_gen ei in
          (EFunc("select", [EVar a; i']), newci) 
      end
    | EFunc(s, es) ->
      let es', newcs = List.split @@ List.map (repl_compound_index_terms fva freshvar_gen) es in
      (EFunc(s, es'), List.flatten newcs)

  let rec repl_compound_index_terms_full fva freshvar_gen rho = function
    | true -> 
      let rho', newc = repl_compound_index_terms fva freshvar_gen rho in
      begin match newc with  
        | [] -> 
          begin match rho' with
            | ELop(And, es) -> repl_compound_index_terms_full fva freshvar_gen rho' false
            | _ -> raise (UnreachableFailure "Root expression is required to be a conjunction")
          end  
        | _ -> 
          begin match rho' with
            | ELop(And, es) -> 
              repl_compound_index_terms_full fva freshvar_gen (ELop(And, es @ newc)) true
            | _ -> raise (UnreachableFailure "Root expression is required to be a conjunction")
          end
        end
      | false -> rho

  let array_bounds_constraints fva array_length e = 
    let rec collect_arrays_bv = function
      | (EVar _ | EArg _ | EConst _) -> []
      | EBop(b, el, er) -> (collect_arrays_bv el) @ (collect_arrays_bv er)
      | EUop(u, e) -> collect_arrays_bv e
      | ELop(lop, es) -> List.flatten @@ List.map collect_arrays_bv es
      | (ELet _ | EExists _ ) -> []
      | EITE(g, tb, fb) -> (collect_arrays_bv g) @ (collect_arrays_bv tb) @ (collect_arrays_bv fb)
      | (EFunc("select", [EVar a; EVar i])) -> 
        if List.mem_assoc a fva then [EVar i] else []
      | EFunc(s, es) -> List.flatten @@ List.map collect_arrays_bv es
    in
    let bvs = collect_arrays_bv e in
    List.map (fun vari ->
      ELop(And, [EBop(Gte, vari, EConst(CInt 0)); EBop(Lt, vari, EConst(CInt array_length))])) bvs

  let run_ackerman_reduction_on_array fva freshvar_gen e = 
    let  tblARVars = Hashtbl.create (List.length fva) in
    let ar_repl_var a ei = 
      match Hashtbl.find_opt tblARVars (a, ei) with 
      | Some efv -> (efv, false)
      | None -> 
        Hashtbl.add tblARVars (a, ei) (freshvar_gen ());
        (Hashtbl.find tblARVars (a, ei), true) 
    in   
    let rec ackerman_reduction e = 
      match e with 
      | (EVar _ | EArg _ | EConst _) -> (e, [])
      | EBop(b, el, er) ->
        let arl, sl = ackerman_reduction el in
        let arr, sr = ackerman_reduction er in
        (EBop(b, arl, arr), sl @ sr) 
      | EUop(u, e) -> 
        let are, se = ackerman_reduction e in
        (EUop(u, are), se)  
      | ELop(lop, es) -> 
        let ares, ses = List.split @@ List.map ackerman_reduction es in
        (ELop(lop, ares), List.flatten ses)
      | (ELet _ | EExists _ ) -> (e, [])
      | EITE(g, tb, fb) -> 
        let arg, sg = ackerman_reduction g in
        let artb, stb = ackerman_reduction tb in
        let arfb, sfb = ackerman_reduction fb in
        (EITE(arg, artb, arfb), sg @ stb @ sfb)
      | (EFunc("select", [EVar a; (EVar _) as ei]) 
        | EFunc("select", [EVar a; (EConst _) as ei])) -> 
        if List.mem_assoc a fva 
        then 
          let freshvar, is_new = ar_repl_var a ei in 
          if is_new then (freshvar, [(a, ei, freshvar)]) else (freshvar, [])  
        else (EFunc("select", [EVar a; ei]), [])
      | EFunc(s, es) -> 
        let ares, ses = List.split @@ List.map ackerman_reduction es in
        (EFunc(s, ares), List.flatten ses)
    in 
    let functional_consistency_constraints repls = 
       List.flatten @@ List.map (fun (a, i, repli) -> 
        List.flatten @@ List.map (fun (a', j, replj) ->
            if (a = a' && (i != j) && ((string_of_smt i) < (string_of_smt j)))
            then [ELop(Or, [EUop(Not, EBop(Eq, i, j)); EBop(Eq, repli, replj)])]
            else []) repls) repls     
    in
    let accounted_mappings repls = 
      List.fold_right (fun (a, i, repli) acc -> 
          match Hashtbl.find_opt acc a with
          | Some n -> Hashtbl.replace acc a (n+1); acc
          | None -> Hashtbl.add acc a 1; acc) repls (Hashtbl.create (List.length fva))
    in
    let rho, repls = ackerman_reduction e in
    let arr_fcs = functional_consistency_constraints repls in
    let arr_accms = accounted_mappings repls in
    let rho = match rho with ELop(And, ces) -> ELop(And, arr_fcs @ ces) 
                           | _ -> raise (UnreachableFailure "Root expression must be conjunction")
    in
    (rho, arr_accms)
  
  let count_conj spec m1 m2 (Conj ces) = 
    let has_array = List.exists 
        (fun (_, t) -> match t with (TArray (TInt, TInt)) -> true | _ -> false)
        (spec.state @ m1.args @ m2.args) in  
    let query_default () = 
      let fvs = spec.state @ m1.args @ m2.args in
      let fvs_decls = String.concat "\n" @@ List.map (
          fun databinding -> mk_var (name_of_binding databinding) (snd databinding)) fvs
      in
      let string_of_mc_query = unlines ~trailing_newline: true (
          ["(set-logic ALL)"
          (* ; smt_of_spec spec *)
          ; fvs_decls
          ; sp "(assert %s)" (string_of_conj (Conj ces))
          ; "(check-sat)"]
        ) 
      in 
      run_mc string_of_mc_query
    in 
    let query_with_array () = 
      (* Procedure for translating the array formulas into LIA formulas
       * 1. Partition the set of free variables in the formula into two subsets: 
       *     - arrays and 
       *     - non-arrays
       * 2. Replace all complex (compund) array index terms 
       *    by "top" universally quantified fresh variables + corresponding constraints.
       *    Perform the replacement from the outermost expresion inwardly
       * 3. Add array bounds constraints for each array index variable  
       * 4. Perform Ackerman Reduction: 
       *    i) Repeat for each occurance of an array-select term (i.e. a[i]) in the formula 
       *    where the index is a "top" universally quantified integer variable, by
       *       - replace a[i] with a fresh variable a_i, keeping track of the association (a, i, a_i)
       *    ii) For each array free variable, and for each pair ((a, i, a_i), (a, j, a_j))
       *    add a constraint corresponding to the functional consistency axiom 
       *       - (i = j ) => (a_i = a_j) or, it's equivalent form 
       *       = not(i = j) \/ (a_i = a_j) 
       * 5. run MC on the output formula and obtain the result #rho
       * 6. For each array free variable, 
       *    calculate the number of unaccounted mappings by 
       *    substracting the number of considered associaition, i.e. (a, i, a_i)s,  
       *    from the length of array: e.g. a_unacc
       * 7. Obtain the final MC by multiplying #rho with PRODUCT (for all a's) |Z|^(a_unacc)  
      *)
      (* Array bounds *)
      let array_length = 4 in
      (* Step 1. Partition of free variables set *)
      let fva, fvna =  List.partition (fun (_, t) ->
          match t with TArray (TInt, TInt) -> true | _ -> false)
          (spec.state @ m1.args @ m2.args)
      in
      let seq = ref 0 in
      let fresh_ivars: ty bindlist ref = ref [] in
      let fresh_ivar_gen = fun () ->   
        seq := !seq + 1;
        let fv = Var ("var_" ^ (string_of_int !seq)) in
        fresh_ivars := (fv, TInt)::(!fresh_ivars);
        EVar fv
      in
      let rho = ELop(And, ces) in
      (* Step 2. Replacement of compound array index terms *)
      let rho = repl_compound_index_terms_full fva fresh_ivar_gen rho true in
      (* Step 3. Add array bounds constraints for index variables*)
      let arr_bv_bc = array_bounds_constraints fva array_length rho in
      let rho = match rho with ELop(And, ces) -> ELop(And, arr_bv_bc @ ces) 
                             | _ -> raise (UnreachableFailure "Root expression must be conjunction")
      in
      (* Step 4. Perform Ackerman Reduction *)
      let rho, acc_arr_mappings = run_ackerman_reduction_on_array fva fresh_ivar_gen rho in  
      
      (* Step 5. Run MC *)
      let count_models fvs e = 
        let fvs_decls = String.concat "\n" @@ List.map (
            fun databinding -> mk_var (name_of_binding databinding) (snd databinding)) fvs
        in 
        let string_of_mc_query = unlines ~trailing_newline: true (
            ["(set-logic ALL)"
            ; fvs_decls 
            ; sp "(assert %s)" (string_of_smt e)
            ; "(check-sat)"]
          ) 
        in 
        run_mc string_of_mc_query
      in match count_models (fvna @ !fresh_ivars) rho with
      | Sat n ->  
        (* Step 6, 7. *)
        let z_size = Int.shift_left 1 (array_length + 1) in
        pfvv "\n>>>Size of Z: %d" z_size;
        pfvv "\n>>>Unaccounted Mappings:";
        let unacc_mappings = List.map (fun (a, _) -> 
            match Hashtbl.find_opt acc_arr_mappings a with
            | Some n -> (a, array_length - n)
            | None -> (a, array_length)) fva 
        in
        List.iter (fun (a, n) -> pfvv "\n>>>%s: %d" (string_of_var a) n) unacc_mappings; 
        let unacc_total = List.fold_right (+) (List.map snd unacc_mappings) 0 in
        (* let rec pow x k acc = if k = 0 then acc else pow x (k-1) (acc * x) in *)
        let mc_unacc_total = Z.pow (Z.of_int z_size) unacc_total in
        pfvv "\n>>>MC for Total Unacccounted Mappings[%d]: %s" unacc_total (Z.to_string mc_unacc_total);
        Sat (Z.mul n mc_unacc_total)  (* (pow z_size unacc_total 1) *)
      | Unsat -> Unsat
      | Unknown -> Unknown
    in
    if has_array then begin
      pfvv "\n MC Conjunction. Case of formula containing arrays";
      query_with_array ()
    end
    else begin
      pfvv "\n MC Conjunction. Case default";
      query_default ()
    end
    
  let count_state spec m1 m2 =     
    let has_array = List.exists 
        (fun (_, t) -> match t with (TArray (TInt, TInt)) -> true | _ -> false)
        (spec.state @ m1.args @ m2.args) in
    (* MC for LIA & String constraints *)
    let query_default () =
      let fvs = spec.state @ m1.args @ m2.args in
      let fvs_decls = String.concat "\n" @@ List.map (
          fun databinding -> mk_var (name_of_binding databinding) (snd databinding)) fvs
      in
      let string_of_mc_query = unlines ~trailing_newline: true (
          [ "(set-logic ALL)"
          (* ; smt_of_spec spec *)
          ; fvs_decls
          ; "(assert true)"
          ; "(check-sat)" ]
        ) 
      in 
      run_mc string_of_mc_query
    in
    (* MC for Constraints with Int Array*)
    let query_with_array () = 
      (* Array bounds *)
      let array_length = 4 in
      (* Step 1. Partition of free variables set *)
      let fva, fvna =  List.partition (fun (_, t) ->
          match t with TArray (TInt, TInt) -> true | _ -> false)
          (spec.state @ m1.args @ m2.args)
      in
      let count_models fvs = 
        let fvs_decls = String.concat "\n" @@ List.map (
            fun databinding -> mk_var (name_of_binding databinding) (snd databinding)) fvs
        in 
        let string_of_mc_query = unlines ~trailing_newline: true (
            ["(set-logic ALL)"
            ; fvs_decls 
            ; "(assert true)"
            ; "(check-sat)"]
          ) 
        in 
        run_mc string_of_mc_query
      in match count_models fvna with
      | Sat n ->  
        (* multiply by the number of all mappings for all arrays *)
        let z_size = Int.shift_left 1 (array_length + 1) in
        pfvv "\n>>>Size of Z: %d" z_size;
        (* let rec pow x k acc = if k = 0 then acc else pow x (k-1) (acc * x) in *)
        let total_mappings = (List.length fva) * array_length in
        (* let mc_total_mappings = pow z_size (total_mappings) 1 in *)
        let mc_total_mappings = Z.pow (Z.of_int z_size) total_mappings in
        pfvv "\n>>>MC for Total Mappings[%d]: %s" total_mappings (Z.to_string mc_total_mappings);
        Sat (Z.mul n  mc_total_mappings)
      | Unsat -> Unsat
      | Unknown -> Unknown
    in
    if has_array then begin 
      pfvv "\n MC State. Case of formula containing arrays";
      query_with_array () end
    else begin
      pfvv "\n MC State. Case default";
      query_default () end
  
  let count_pred spec m1 m2 p = 
    count_conj spec m1 m2 (Conj [exp_of_predP p])
end 
  
let count_state = 
  curry3 @@ memoize @@ fun (spec, m1, m2) ->
  pfvv "\n=== MC State ===\n";
  let result =  PredicateModelCount.count_state spec m1 m2 in
  pfvv "\n=== MC State Result: ===\n%s\n--------------------------\n" 
    (begin match result with
       | Sat c -> sp "Sat; count: %s" (Z.to_string c)
       | Unsat -> "Unsat"
       | Unknown -> "Unknown"
     end);
  result

let count_pred spec m1 m2 pP =
  pfvv "\n=== MC Pred ===";
  let result = PredicateModelCount.count_pred spec m1 m2 pP in
  pfvv "\n=== MC Pred Result: %s ===\n%s\n--------------------------\n"
    (string_of_predP pP)
    (begin match result with
       | Sat c -> sp "Sat; count: %s" (Z.to_string c)
       | Unsat -> "Unsat"
       | Unknown -> "Unknown"
     end);
  result

let count_conj : spec -> method_spec -> method_spec -> Phi.conjunction -> mc_result = 
  curry4 @@ memoize @@ fun (spec, m1, m2, c) ->
  pfvv "\n=== MC Conjunction ===\n";
  let result = PredicateModelCount.count_conj spec m1 m2 c in
  pfvv "\n=== MC State Conjunction: %s ===\n%s\n--------------------------\n"
    (string_of_conj c)
    (begin match result with
       | Sat c -> sp "Sat; count: %s" (Z.to_string c)
       | Unsat -> "Unsat"
       | Unknown -> "Unknown"
     end);
  result
