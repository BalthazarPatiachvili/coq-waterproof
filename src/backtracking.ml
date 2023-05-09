open Pp

(**
  Exception raised if no proof of the goal is found
*)
exception SearchBound

(**
  Trace atome type

  Can be read as `(is_success, depth, current_proof_state`, print_function_option, hint_name, hint_db_source)`
*)
type trace_atom = bool * int * t * t

(**
  Debug type
*)
type trace = {
  log: bool; (** Are tried hints printed ? *)
  current_depth: int; (** The current depth of the search *)
  trace: trace_atom list (** The full trace of tried hints *)
}

(**
  Increases the debug depth by 1
*)
let incr_trace_depth (trace: trace): trace = {log = trace.log; current_depth = trace.current_depth + 1; trace = trace.trace}

(**
  Returns a [trace] value corresponding to [no trace recording]
*)
let no_trace: trace = {log = false; current_depth = 0; trace = []}

(**
  Creates a [trace] value given a boolean indicating if tried hints are printed
*)
let new_trace (log: bool): trace = {log = log; current_depth = 0; trace = []}

(**
  Creates a trace containing only one atom 
*)
let singleton_trace (log: bool) (is_success: bool) (depth: int) (hint_name: t) (src: t): trace =
  {
    log;
    current_depth = 1;
    trace = [(is_success, depth, hint_name, src)];
  }

(**
  Prints an info atom, i.e an element of the info trace
*)
let pr_trace_atom ((is_success, d, hint, src): trace_atom): t =
  str (String.make (d + 1) ' ') ++ str (if is_success then "✓" else "×") ++ spc () ++ hint ++ str " in (" ++ src ++ str ")."

(**
  Prints the complete info trace
*)
let pr_trace (trace: trace): unit =
  Feedback.msg_notice (str "Trace:");
  Feedback.msg_notice (prlist_with_sep fnl pr_trace_atom trace.trace)

(**
  Returns the trace atoms that have been actually applied during {! Wauto.wauto}

  It is supposed here that the given [trace] has not been modified since the end of {! Wauto.wauto}.
*)
let keep_applied (trace: trace_atom list): (int * t * t) list = 
  List.rev @@ 
  List.filter_map (fun (is_success, depth, hint, src) ->
    match is_success with
      | true -> Some (depth, hint, src)
      | false -> None
  ) trace
