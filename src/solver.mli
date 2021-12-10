open Util

type solve_result

(* Execute CVC4/Z3/etc... *)
val run_solver : Smt.exp -> solve_result