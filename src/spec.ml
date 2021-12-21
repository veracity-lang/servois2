(* Module for 
 *
 *)

open Util
open Smt

type method_spec =
  { name : string
  ; args : ty bindlist
  ; ret  : ty binding
  ; pre  : exp
  ; post : exp
  }

type spec =
  { preds    : pred list
  ; state_eq : exp
  ; state    : ty bindlist
  ; methods  : method_spec list
  }

let get_method spec mname = List.find (fun m -> m.name = mname) spec.methods 
