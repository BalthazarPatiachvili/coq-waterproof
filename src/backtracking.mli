(**
  Trace atome type

  Can be read as `(is_success, depth, print_function_option, hint_name, hint_db_source)`
*)
type trace_atom =
  bool
  * int
  * Pp.t
  * Pp.t

(**
  Trace type
*)
type trace = {
  log_level: Hints.debug; (** Log level ([Off], [Info] or [Debug]) *)
  current_depth: int; (** The current depth of the search *)
  trace: trace_atom list ref (** The full trace of tried hints *)
}

(**
  Creates a [trace] value from a [Hints.debug] value
*)
val new_trace : Hints.debug -> trace

(**
  Returns a [trace] value corresponding to `no debug`
*)
val no_trace : unit -> trace

(**
  Prints the complete info trace
*)
val pr_trace : Environ.env -> Evd.evar_map -> trace -> unit

(**
  Returns the trace atoms that have been actually applied during [wauto]

  It is supposed here that the given [trace] has not been modified since the end of [wauto] and that [wauto] is successful, i.e it succeed to solve the goal
*)
val keep_applied :
  trace_atom list -> (int * Pp.t * Pp.t) list
