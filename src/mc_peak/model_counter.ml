open Smt
open Spec
open Phi
open Util
open Solve

type mc_result = 
  | Sat of int
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

  let args = [| ""; "-v"; "0"; "-bi"; string_of_int bound_int; "-i"; smt_fname |]

  let line_count_regex = Str.regexp {|.*report bound: [0-9]+ count: \([0-9]+\) time:.*.*|}

  let rec parse_mc_report ls = 
    match ls with
    | [] -> Unknown
    | l::ls' ->
       if Str.string_match line_count_regex l 0 then begin
         Sat (int_of_string @@ Str.matched_group 1 l) end
       else parse_mc_report ls'
    
  let parse_sat (sout, serr) = 
    match sout, serr with
    | [], [] -> Unknown
    | l::ls, _ -> Sat (int_of_string l)
    | [], rls -> parse_mc_report rls 

  let rec parse_output = function (sout, serr) ->  
    match sout with
    | [] -> Unknown
    | l::ls ->
      if (String.equal l "sat") then parse_sat (ls, serr)  
      else if (String.equal l "unsat") then Unsat else parse_output (ls, serr) 
   
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
    create_smt_file mc_query MC.smt_fname;
    let result = run_model_counter (module MC) |> MC.parse_output in
    pfv "\nModel counting for PREDICATE: \n|?| %s \n|-> Result: %s\n--------------------------\n" 
      (Str.global_replace (Str.regexp "\n") "\n|?| " mc_query) 
      (begin match result with
         | Sat c -> sp "Sat; bound %d; count: %d" MC.bound_int  c
         | Unsat -> "Unsat"
         | Unknown -> "Unknown"
       end);
    remove_smt_file MC.smt_fname;
    result

  let count_state spec m1 m2 =     
    let string_of_mc_query = unlines ~trailing_newline: true (
        [ "(set-logic ALL)"
        ; smt_of_spec spec
        ; "(assert true)"
        ; "(check-sat)" ]
      ) 
    in 
    run_mc string_of_mc_query

  let count_pred spec m1 m2 p = 
    let string_of_mc_query = unlines ~trailing_newline: true (
        ["(set-logic ALL)"
        ; smt_of_spec spec
        ; sp "(assert %s)" (string_of_predP p)
        ; "(check-sat)"]
      ) 
    in 
    run_mc string_of_mc_query
end

let count_state = PredicateModelCount.count_state 
let count_pred = PredicateModelCount.count_pred
 
