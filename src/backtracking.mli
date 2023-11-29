(******************************************************************************)
(*                  This file is part of Waterproof-lib.                      *)
(*                                                                            *)
(*   Waterproof-lib is free software: you can redistribute it and/or modify   *)
(*    it under the terms of the GNU General Public License as published by    *)
(*     the Free Software Foundation, either version 3 of the License, or      *)
(*                    (at your option) any later version.                     *)
(*                                                                            *)
(*     Waterproof-lib is distributed in the hope that it will be useful,      *)
(*      but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*       MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the         *)
(*               GNU General Public License for more details.                 *)
(*                                                                            *)
(*     You should have received a copy of the GNU General Public License      *)
(*   along with Waterproof-lib. If not, see <https://www.gnu.org/licenses/>.  *)
(*                                                                            *)
(******************************************************************************)

(**
  Trace atome type

  Can be read as [(is_success, depth, hint_name, hint_db_source)]
*)
type trace_atom = bool * int * Pp.t * Pp.t

(**
  Trace type
*)
type trace = {
  log: bool; (** Are tried hints printed ? *)
  current_depth: int; (** The current depth of the search *)
  trace: trace_atom list (** The full trace of tried hints *)
}

(**
  Exception raised if no proof of the goal is found
*)
exception SearchBound of trace

(**
  Increases the debug depth by 1
*)
val incr_trace_depth : trace -> trace

(**
  [trace] value corresponding to "no trace recording"
*)
val no_trace : trace

(**
  Creates a [trace] value given a boolean indicating if tried hints are printed
*)
val new_trace : bool -> trace

(**
  Creates a trace containing only one atom 
*)
val singleton_trace : bool -> Pp.t -> Pp.t -> trace

(**
  Marks all the trace atoms contained in the given [trace] as unsuccessful
*)
val failed : trace -> trace

(**
  Concatenates the two given traces
*)
val merge_traces : trace -> trace -> trace

(**
  Prints an info atom, i.e an element of the info trace
*)
val pr_trace_atom : trace_atom -> Pp.t

(**
  Prints the complete info trace
*)
val pr_trace : trace -> unit

(**
  Returns the trace atoms that have been actually applied during a [trace tactic] (like {! Wp_auto.wp_auto})

  It is supposed here that the given [trace] has not been modified after getting it from the [trace tactic].
*)
val keep_applied : trace -> trace
