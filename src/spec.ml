(* Module for 
 *
 *)

open Util
open Yaml_util
open Smt
open Yaml

type method_spec =
  { name  : string
  ; args  : ty bindlist
  ; ret   : ty binding
  ; pre   : exp
  ; post  : exp
  ; terms : (ty * (exp list)) list
  }

type spec =
  { name     : string
  ; preds    : pred list
  ; state_eq : exp
  ; state    : ty bindlist
  ; methods  : method_spec list
  }


let method_spec_of_yaml (y : Yaml.value) : method_spec =
  (* Method dictionary *)
  let d = get_dict y "Method isn't dict" in
  let get_field s =
    assoc_dict s d @@ sp "Method is missing '%s' field" s
  in
  
  (* Method dictionary fields *)
  let f_name         = get_field "name" in
  let f_args         = get_field "args" in
  let f_return       = get_field "return" in
  let f_requires     = get_field "requires" in
  let f_ensures      = get_field "ensures" in
  let f_terms        = get_field "terms" in

  raise @@ NotImplemented ""


let spec_of_yaml (y : Yaml.value) : spec =
  (* Outermost dictionary *)
  let d = get_dict y "Yaml isn't dict" in
  let get_field s =
    assoc_dict s d @@ sp "Missing '%s' field" s
  in

  (* Outermost dictionary fields *)
  let f_name         = get_field "name" in
  let f_state        = get_field "state" in
  let f_methods      = get_field "methods" in
  let f_predicates   = get_field "predicates" in
  let f_states_equal = get_field "states_equal" in

  (* Name *)
  let name = get_string f_name "'name' isn't string" in

  (* State *)
  let state = failwith "" in

  (* Methods *)
  let methods =
    let l = get_list f_methods "'methods' isn't list" in
    List.map method_spec_of_yaml l
  in

  (* Predicates *)
  let preds = failwith "" in

  (* States_equal *)
  let state_eq = failwith "" in

  { name; state; methods; preds; state_eq }