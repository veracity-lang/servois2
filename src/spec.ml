open Util
open Yaml_util
open Smt
open Yaml
open Smt_parsing


type term_list = ty * (exp list)

type method_spec =
  { name  : string
  ; args  : ty bindlist
  ; ret   : ty bindlist
  ; pre   : exp
  ; post  : exp
  ; terms : term_list list
  }

type spec =
  { name     : string
  ; preds    : pred_sig list
  ; state_eq : exp
  ; state    : ty bindlist
  ; methods  : method_spec list
  }

let has_err_state spec = List.exists (fun binding -> name_of_binding binding = "err") spec.state

let lift (spec : spec) : spec =
    if has_err_state spec then spec
    else let new_state = (Var "err", TBool) :: spec.state in
    let new_state_eq = ELop(Or, [ELop (And, [EVar(Var "err"); EVar(VarPost "err")]); ELop(And, [EUop(Not, EVar(Var "err")); EUop(Not, EVar(VarPost "err")); spec.state_eq])]) in
    let lift_method m = { m with pre = EConst(CBool(true)); post =
        ELop(Or, [
            ELop(And, [EVar(Var "err"); EVar(VarPost "err")]); 
            ELop(And, [EUop(Not, EVar(Var "err")); EUop(Not, EVar(VarPost "err")); m.pre; m.post]);
            ELop(And, [EUop(Not, EVar(Var "err")); EVar(VarPost "err"); EUop(Not, m.pre)])
        ]) } in
    let new_methods = List.map lift_method spec.methods in
    { spec with state_eq = new_state_eq; state = new_state; methods = new_methods }

let get_method (spec : spec) mname : method_spec = List.find (fun (m : method_spec) -> m.name = mname) (spec.methods) 

(*** Methods for converting Yaml ADT to spec ***)

let ty_of_yaml (y : Yaml.value) : ty =
  get_string y "Type isn't string" |>
  ty_of_string

let binding_of_yaml (y : Yaml.value) : ty binding =
  let d = get_dict y "Binding isn't dict" in
  let get_field s =
    assoc_dict s d @@ sp "Binding is missing '%s' field" s
  in

  let f_name = get_field "name" in
  let f_type = get_field "type" in

  let name = get_string f_name "'name' isn't string" in
  let ty = ty_of_yaml f_type in

  Var name, ty

let pred_of_yaml (y : Yaml.value) : pred_sig =
  let d = get_dict y "Pred isn't dict" in
  let get_field s =
    assoc_dict s d @@ sp "Pred is missing '%s' field" s
  in

  let f_name = get_field "name" in
  let f_type = get_field "type" in

  let name = get_string f_name "'name' isn't string" in
  let ty =
    get_list f_type "'type' isn't list" |>
    List.map ty_of_yaml
  in

  PredSig (name, ty)

let exp_of_yaml (y : Yaml.value) : exp =
  let s =
    match y with
    | `String s -> s
    | `Float f  -> string_of_float f
    | _ -> raise @@ BadInputFormat "Exp isn't float or string"
  in exp_of_string s

let method_spec_of_yaml (y : Yaml.value) : method_spec =
  (* Method dictionary *)
  let d = get_dict y "Method isn't dict" in
  let get_field s =
    assoc_dict s d @@ sp "Method is missing '%s' field" s
  in
  
  (* Method dictionary fields *)
  let f_name     = get_field "name" in
  let f_args     = get_field "args" in
  let f_return   = get_field "return" in
  let f_requires = get_field "requires" in
  let f_ensures  = get_field "ensures" in
  let f_terms    = get_field "terms" in

  (* Name *)
  let name = get_string f_name "'name' isn't name" in

  (* Args *)
  let args =
    get_list f_args "'args' isn't list" |>
    List.map binding_of_yaml
  in

  (* Return *)
  let ret = 
    get_list f_return "'return' isn't list" |>
    List.map binding_of_yaml
  in

  (* Requires *)
  let pre = exp_of_yaml f_requires in

  (* Ensures *)
  let post = exp_of_yaml f_ensures in

  let terms =
    get_dict f_terms "'terms' isn't dict" |>
    List.map @@
    fun (s,v) ->
      ty_of_string s,
      get_list v "terms aren't list" |>
      List.map exp_of_yaml
  in

  { name; args; ret; pre; post; terms }


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
  let state =
    get_list f_state "'state' isn't list" |>
    List.map binding_of_yaml
  in

  (* Methods *)
  let methods =
    let l = get_list f_methods "'methods' isn't list" in
    List.map method_spec_of_yaml l
  in

  (* Predicates *)
  let preds =
    get_list f_predicates "'predicates' isn't list" |>
    List.map pred_of_yaml
  in

  (* State equality predicate *)
  let state_eq =
    let d = get_dict f_states_equal "'states_equal' isn't dict" in
    assoc_dict "definition" d "Missing 'defintion' field" |>
    exp_of_yaml
  in

  { name; state; methods; preds; state_eq }



module Spec_ToMLString = struct
  let pred_sig (PredSig (s, t)) =
    "PredSig " ^
    ToMLString.pair ToMLString.str (ToMLString.list Smt_ToMLString.ty) (s,t)

  let term_list =
    ToMLString.pair Smt_ToMLString.ty (ToMLString.list Smt_ToMLString.exp)

  let method_spec {name;args;ret;pre;post;terms} =
    sp "{name=%s;\nargs=%s;\nret=%s;\npre=%s;\npost=%s;\nterms=%s}"
    (ToMLString.str name)
    (Smt_ToMLString.ty_bindlist args)
    (Smt_ToMLString.ty_bindlist ret)
    (Smt_ToMLString.exp pre)
    (Smt_ToMLString.exp post)
    (ToMLString.list term_list terms)

  let spec {name;preds;state_eq;state;methods} =
    sp "{name=%s;\npreds=%s;\nstate_eq=%s;\nstate=%s;\nmethods=%s}"
    (ToMLString.str name)
    (ToMLString.list pred_sig preds)
    (Smt_ToMLString.exp state_eq)
    (Smt_ToMLString.ty_bindlist state)
    (ToMLString.list method_spec methods)

end
