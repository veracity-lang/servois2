open Util

type solve_result =
  | Valid
  | Invalid of string
  | Unknown


(* We instantiate the module with specific provers, e.g. CVC4, Z3 *)
module type Prover = sig
  val run : string -> solve_result
end


module ProverCVC4 : Prover = struct
  let exec_paths =
    [ "/usr/local/bin/cvc4"
    ; "/usr/bin/cvc4"
    ]

  let args =
    [| ""; "--lang"; "smt2"; "--produce-models" |]

  let run (smt : string) : solve_result =
    let exec = find_exec "CVC4" exec_paths in
    let sout, serr = run_exec exec args smt in
    Printf.printf "* * * OUT * * * \n%s\n* * * ERR * * * \n%s\n* * * * * *\n"
      (String.concat "\n" sout) (String.concat "\n" serr);
    raise @@ NotImplemented "run"

end