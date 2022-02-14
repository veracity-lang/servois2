(* Module for conducting the phi synthesis algorithm 
 * Algorithm comes from Fig. 1 of TACAS'18.
 *)

open Util
open Smt
open Solve
open Spec
open Phi
open Provers
open Choose
open Smt_parsing
open Predicate

type synth_options =
  { preds : pred list option
  ; prover : (module Prover)
  ; lift : bool
  ; timeout : float option
  }

let default_synth_options =
  { preds = None
  ; prover = (module Provers.ProverCVC4)
  ; lift = true
  ; timeout = None
  }

type benches =
  { predicates : int
  ; predicates_filtered : int
  ; smtqueries : int
  ; time : float
  }

let last_benchmarks = ref {predicates = 0; predicates_filtered = 0; smtqueries = 0; time = 0.0}

let string_of_benches benches = sp "predicates, %d\npredicates_filtered, %d\nsmtqueries, %d\ntime, %.6f" benches.predicates benches.predicates_filtered benches.smtqueries benches.time

type counterex = exp bindlist


(* Assumes there are no EArgs *)
let mangle_method_vars (index : int) {name;args;ret;pre;post;terms} : method_spec =
  
  (* Get names of arguments and returns *)
  let name_of_var = function
    | Var s, _ -> s
    | _     -> raise @@ UnreachableFailure "Unexpected var variant"
  in let local_names = List.map name_of_var args @ List.map name_of_var ret in

  (* Convert Var and VarPost to VarM and VarMPost respectively,
   * so long as variable is local to method *)
  let mangle_var = function
    | Var v ->
      if List.mem v local_names
      then VarM (v, index)
      else Var v
    | VarPost v ->
      if List.mem v local_names
      then VarMPost (v, index)
      else VarPost v
    | VarM _ | VarMPost _ ->
      raise @@ UnreachableFailure "Variable is already mangled"
  in

  (* Recurse down expression, mangling variables *)
  let rec mangle_exp = function
    | EConst c -> EConst c
    | EVar v -> EVar (mangle_var v)
    | EArg n ->
      raise @@ UnreachableFailure "EArg in mangling stage"
    | EBop (b, e1, e2) -> 
      EBop (b, mangle_exp e1, mangle_exp e2)
    | EUop (u, e) ->
      EUop (u, mangle_exp e)
    | ELop (l, el) ->
      ELop (l, List.map mangle_exp el)
    | ELet (el, e) ->
      ELet ( List.map (fun (s,e) -> s, mangle_exp e) el, 
              mangle_exp e )
    | EITE (b, t, f) ->
      EITE (mangle_exp b, mangle_exp t, mangle_exp f)
    | EFunc (s, el) ->
      EFunc (s, List.map mangle_exp el)
  in
  
  (* Mangle variables in appropriate fields of method spec *)
  let pre = mangle_exp pre in
  let post = mangle_exp post in
  let terms =
    List.map (fun (ty, el) -> ty, List.map mangle_exp el)
      terms
  in

  {name;args;ret;pre;post;terms}


let synth ?(options = default_synth_options) spec m n =
    let spec' = if options.lift then lift spec else spec in

    let m_spec = get_method spec m |> mangle_method_vars 1 in
    let n_spec = get_method spec n |> mangle_method_vars 2 in

    let preds = match options.preds with None -> generate_predicates spec' m_spec n_spec | Some x -> x in
    (* TODO: do predicate filtering *)
    let bench = ref { !last_benchmarks with predicates = List.length preds; predicates_filtered = List.length preds } in
    let synth_inner preds prover (timelimit : float option) spec m_spec n_spec =
      let phi = ref @@ Disj [] in
      let phi_tilde = ref @@ Disj [] in
      (* I'm pretty sure this is preferable to carrying it around in an option: *)
      let init_time = Sys.time () in
      let final_time = match timelimit with None -> Float.infinity | Some s -> Float.add init_time s in
      let rec refine (h : conjunction) (p_set : pred list) : unit =
        if Float.compare (Sys.time ()) final_time > 0 then raise (Failure "timeout failure") else
        let solve_inst = solve prover spec m_spec n_spec in
        let pred_smt = List.map smt_of_pred p_set in
        begin match solve_inst pred_smt @@ commute (spec.precond) h with
          | Unsat -> phi := add_disjunct h !phi
          | Unknown -> raise @@ Failure "commute failure" (* TODO: Better error behavior? Backtracking? *)
          | Sat s -> begin let com_cex = parse_pred_data s in
            match solve_inst pred_smt @@ non_commute (spec.precond) h with
              | Unsat -> phi_tilde := add_disjunct h !phi_tilde
              | Unknown -> raise @@ Failure "non_commute failure"
              | Sat s -> begin let non_com_cex = parse_pred_data s in
                let p = !choose { solver = solve_inst; spec = spec; h = h; choose_from = p_set; cex_ncex = (com_cex, non_com_cex) } in
                    refine (add_conjunct (atom_of_pred p) h) (remove p p_set);
                    refine (add_conjunct (not_atom @@ atom_of_pred p) h) (remove p p_set)
                end
            end
        end in
      let init_smt_queries = !Provers.n_queries in
      begin try refine (Conj []) (List.sort (fun x y -> complexity x - complexity y) @@ preds) 
          with | Failure f -> print_string f; print_newline () (* TODO: Make this error handling better? *)
      end;
      bench := { !bench with
          smtqueries = !Provers.n_queries - init_smt_queries;
          time = Float.sub (Sys.time ()) init_time };
      !phi, !phi_tilde in
    let ret = synth_inner preds options.prover options.timeout spec' m_spec n_spec in
    last_benchmarks := !bench; ret
  
