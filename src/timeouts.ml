(* Timeout configuration, shared by Servois2, Veracity and ConQuoer.
 *
 * There are three distinct limits, and they are not interchangeable:
 *
 *   query    one SMT check-sat. Enforced by the solver itself, via its own
 *            command-line flag (see [prover_args]) -- every prover we support
 *            has one. Applies to both `verify` and `infer`.
 *   synth    a whole condition-synthesis run. Wall-clock, enforced here by
 *            SIGALRM (Util.run_with_time_limit). `infer` only.
 *   lattice  lattice construction within synthesis. Same mechanism.
 *
 * Resolution follows the order Rundir already uses for the output root: a value
 * supplied by the calling tool wins, else this tool's own CLI flag, else the
 * environment, else the default. So a tool run standalone is configured by its
 * flags, and a tool run as a library takes its caller's settings.
 *
 * Note on mechanism: `query` deliberately does *not* use SIGALRM. There is one
 * ITIMER_REAL per process, and synthesis already holds it for the duration of a
 * run -- arming a second one per query would overwrite the outer timer and its
 * cleanup would cancel it, silently disabling the synth timeout. The solvers'
 * native limits have no such interaction.
 *)

type t =
  { query   : float        (* seconds, per SMT check-sat *)
  ; synth   : float option (* seconds; None = unbounded *)
  ; lattice : float option (* seconds; None = unbounded *)
  }

(* 120s per query matches the limit CVC5 was previously pinned to. 30s of
   lattice construction was the old --lattice-timeout default. Synthesis as a
   whole was unbounded, and stays that way: it is bounded in practice by the
   query limit times the number of queries. *)
let default = { query = 120.; synth = None; lattice = Some 30. }

exception Bad_timeout of string * string

let () =
  Printexc.register_printer @@ function
  | Bad_timeout (name, s) ->
    Some (Printf.sprintf
            "invalid timeout for %s: %S (expected seconds > 0, or \"none\")" name s)
  | _ -> None

let float_of_arg name s =
  match float_of_string_opt (String.trim s) with
  | Some f when f > 0. -> f
  | _ -> raise (Bad_timeout (name, s))

(* The optional limits accept "none"/"off"/"0" to mean "no limit". *)
let opt_of_arg name s =
  match String.lowercase_ascii (String.trim s) with
  | "none" | "off" | "0" -> None
  | _ -> Some (float_of_arg name s)

let env_query   = "SMT_TIMEOUT_QUERY"
let env_synth   = "SMT_TIMEOUT_SYNTH"
let env_lattice = "SMT_TIMEOUT_LATTICE"

let of_env (base : t) : t =
  let str name = Sys.getenv_opt name in
  { query =
      (match str env_query with
       | Some s -> float_of_arg env_query s
       | None -> base.query)
  ; synth =
      (match str env_synth with
       | Some s -> opt_of_arg env_synth s
       | None -> base.synth)
  ; lattice =
      (match str env_lattice with
       | Some s -> opt_of_arg env_lattice s
       | None -> base.lattice)
  }

(* The one source of truth. CLIs overwrite it after parsing their flags; an
   embedding tool overwrites it before driving the library. *)
let current : t ref = ref (of_env default)

let get () = !current
let set (t : t) = current := t

let string_of_opt = function None -> "none" | Some f -> Printf.sprintf "%gs" f

(* Arg entries for the three limits, defined once so that every CLI -- servois2,
   vcy, conquoer -- exposes the same flag names, help text and defaults. A tool
   run standalone is configured by these; a tool run as a library instead takes
   whatever its caller passed to [set]. *)
let speclist : (string * Arg.spec * string) list =
  let upd f = Arg.String (fun s -> current := f !current s) in
  [ "--timeout-query",
    upd (fun t s -> { t with query = float_of_arg "--timeout-query" s }),
    Printf.sprintf
      "SECS Time limit for a single SMT query, enforced by the solver (default %gs)"
      default.query
  ; "--timeout-synth",
    upd (fun t s -> { t with synth = opt_of_arg "--timeout-synth" s }),
    Printf.sprintf
      "SECS Time limit for a whole synthesis run, or \"none\" (infer only; default %s)"
      (string_of_opt default.synth)
  ; "--timeout-lattice",
    upd (fun t s -> { t with lattice = opt_of_arg "--timeout-lattice" s }),
    Printf.sprintf
      "SECS Time limit for lattice construction, or \"none\" (infer only; default %s)"
      (string_of_opt default.lattice)
  ]

(* The solver's own per-query limit, as command-line flags appended to the
   prover invocation. Driving these from [query] is what makes the limit
   configurable at all: it used to be hardcoded for CVC5 and absent entirely for
   Z3, which therefore ran unbounded. Each returns "unknown" on expiry rather
   than failing, which the provers' output parser already handles. *)
let prover_args (prover_name : string) : string array =
  let t = get () in
  let ms = int_of_float (Float.round (t.query *. 1000.)) in
  match prover_name with
  (* Per check-sat, not cumulative, so it fits the --incremental multi-check-sat
     usage. *)
  | "CVC4" | "CVC5" -> [| Printf.sprintf "--tlimit-per=%d" ms |]
  | "Z3"            -> [| Printf.sprintf "-t:%d" ms |]
  | "Yices"         -> [| Printf.sprintf "--timeout=%d"
                            (int_of_float (Float.round (Float.max 1. t.query))) |]
  | _               -> [||]
