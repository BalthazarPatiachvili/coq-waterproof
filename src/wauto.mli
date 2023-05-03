open Backtracking

(**
  Exception raised if no proof of the goal is found
*)
exception SearchBound

(**
  Updates the given debug and print informations according to the field [Hints.debug]
*)
val tclLOG :
  trace ->
  (Environ.env -> Evd.evar_map -> Pp.t * Pp.t) ->
  'a Proofview.tactic ->
  'a Proofview.tactic

(**
  Prints "idtac" if the [Hints.debug] level is [Info]
*)
val pr_info_nop : trace -> unit

(**
  Tries the given tactic and calls an info printer if it fails
*)
val tclTRY_dbg :
  trace ->
  (trace -> unit) ->
  (Environ.env -> Evd.evar_map -> trace -> unit) ->
  (trace -> unit) ->
  unit Proofview.tactic ->
  unit Proofview.tactic

(**
  Creates a function that takes a hint database and returns a hint list
*)
val hintmap_of :
  Environ.env ->
  Evd.evar_map ->
  Names.Id.Pred.t ->
  Evd.econstr ->
  (Hints.hint_db -> Hints.FullHint.t list)

(**
  Searches a sequence of at most [n] tactics within [db_list] and [lems] that solves the goal

  The goal cannot contain evars
*)
val search : trace -> int -> Hints.hint_db list -> Tactypes.delayed_open_constr list -> unit Proofview.tactic

(**
  Waterproof auto

  This function is a rewrite around coq-core.Auto.auto with the same arguments to be able to retrieve which tactics have been used in case of success.

  The given [trace] will be updated with the trace at the end of the execution (consider using).
*)
val wauto :
  trace ->
  int ->
  Tactypes.delayed_open_constr list ->
  string list ->
  unit Proofview.tactic
