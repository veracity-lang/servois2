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
  ; preamble : string option
  ; preds    : pred_sig list
  ; state_eq : exp
  ; precond  : exp
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

let get_method (spec : spec) mname : method_spec = try List.find (fun (m : method_spec) -> m.name = mname) (spec.methods)
    with Not_found -> failwith @@ sp "Could not find method %s." mname

let prefix_method_arg (is_left : bool) (name : string) = sp "m%d_%s" (if is_left then 1 else 2) name
let name_method_arg (m : method_spec) (is_left : bool) i = (name_of_binding @@ List.nth m.args i) |> prefix_method_arg is_left
let name_method_args (m : method_spec) (is_left : bool) : exp -> exp = name_method_arg m is_left |> name_arguments

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
    | `Float f  -> int_of_float f |> string_of_int
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

  (* Convert an indexed argument to a named variable *)
  let bake_arg (index : int) : exp =
    match List.nth_opt args (index - 1) with
    | Some (v_name, _) -> EVar v_name
    | None -> raise @@ Failure (sp "Invalid argument index $%d in method '%s'" index name)
  in

  (* Bake all arguments in an expression *)
  let rec bake_args (exp : exp) : exp =
    match exp with
    | EVar _ | EConst _ -> exp
    | EArg n -> bake_arg n
    | EBop (b, e1, e2) -> 
      EBop (b, bake_args e1, bake_args e2)
    | EUop (u, e) ->
      EUop (u, bake_args e)
    | ELop (l, el) ->
      ELop (l, List.map bake_args el)
    | ELet (el, e) ->
      ELet ( List.map (fun (s,e) -> s, bake_args e) el, 
             bake_args e )
    | EITE (b, t, f) ->
      EITE (bake_args b, bake_args t, bake_args f)
    | EFunc (s, el) ->
      EFunc (s, List.map bake_args el)
  in

  (* Return *)
  let ret = 
    get_list f_return "'return' isn't list" |>
    List.map binding_of_yaml
  in

  (* Requires *)
  let pre = exp_of_yaml f_requires |> bake_args in

  (* Ensures *)
  let post = exp_of_yaml f_ensures |> bake_args in

  let terms =
    get_dict f_terms "'terms' isn't dict" |>
    List.map @@
    fun (s,v) ->
      ty_of_string s,
      get_list v "terms aren't list" |>
      List.map exp_of_yaml |>
      List.map bake_args
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

  let preamble = try let f_preamble = get_field "preamble" in Some(get_string f_preamble "'preamble' isn't string") with 
      | BadInputFormat _ -> None in

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

  (* Precondition *)
  let precond = try let f_precond = get_field "precondition" in exp_of_yaml f_precond with 
      | BadInputFormat _ -> EConst (CBool true)
  in

  { name = name
  ; preamble = preamble
  ; preds = preds
  ; state_eq = state_eq
  ; precond = precond
  ; state = state
  ; methods = methods }



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

  let spec {name;preamble;preds;state_eq;precond;state;methods} =
    sp "{name=%s;\n%spreds=%s;\nstate_eq=%s;\nprecondition=%s;\nstate=%s;\nmethods=%s}"
    (ToMLString.str name)
    begin match preamble with Some s -> sp "%s preamble" (ToMLString.str s) | None -> "" end
    (ToMLString.list pred_sig preds)
    (Smt_ToMLString.exp state_eq)
    (Smt_ToMLString.exp precond)
    (Smt_ToMLString.ty_bindlist state)
    (ToMLString.list method_spec methods)

end
