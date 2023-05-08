open Auto
open Hints
open Names
open Proofview
open Proofview.Notations
open Pp
open Tactics
open Termops
open Unification
open Util

open Backtracking

(* All the definitions below come from coq-core hidden library (i.e not visible in the API) *)

let auto_core_unif_flags_of st1 st2 = {
  modulo_conv_on_closed_terms = Some st1;
  use_metas_eagerly_in_conv_on_closed_terms = true;
  use_evars_eagerly_in_conv_on_closed_terms = false;
  modulo_delta = st2;
  modulo_delta_types = TransparentState.full;
  check_applied_meta_types = false;
  use_pattern_unification = false;
  use_meta_bound_pattern_unification = true;
  allowed_evars = Evarsolve.AllowedEvars.all;
  restrict_conv_on_strict_subterms = false;
  modulo_betaiota = false;
  modulo_eta = true;
}

let auto_unif_flags_of st1 st2 =
  let flags = auto_core_unif_flags_of st1 st2 in {
  core_unify_flags = flags;
  merge_unify_flags = flags;
  subterm_unify_flags = { flags with modulo_delta = TransparentState.empty };
  allow_K_in_toplevel_higher_order_unification = false;
  resolve_evars = true
}

let auto_unif_flags =
  auto_unif_flags_of TransparentState.full TransparentState.empty

let unify_resolve_nodelta h = Hints.hint_res_pf ~with_evars:true ~flags:auto_unif_flags h

let exact h =
  Goal.enter begin fun gl ->
    let env = Goal.env gl in
    let sigma = Goal.sigma gl in
    let sigma, c = Hints.fresh_hint env sigma h in
    let sigma, t = Typing.type_of env sigma c in
    let concl = Goal.concl gl in
    if occur_existential sigma t || occur_existential sigma concl then
      let sigma = Evd.clear_metas sigma in
      try
        let sigma = Unification.w_unify env sigma CONV ~flags:auto_unif_flags concl t in
        Unsafe.tclEVARSADVANCE sigma <*>
        exact_no_check c
      with e when CErrors.noncritical e -> tclZERO e
    else Unsafe.tclEVARS sigma <*> exact_check c
  end

let exists_evaluable_reference (env: Environ.env) (evaluable_ref: Tacred.evaluable_global_reference) = match evaluable_ref with
  | Tacred.EvalConstRef _ -> true
  | Tacred.EvalVarRef v -> try ignore(Environ.lookup_named v env); true with Not_found -> false

(* All the definitions below are inspired by the coq-core hidden library (i.e not visible in the API) but modified for Waterproof *)

let agregateTrace (trace1: trace) (trace2: trace): trace =
  { trace2 with trace = List.append trace1.trace trace2.trace }

let agregateTraceList (traces: trace list): trace =
  List.fold_left agregateTrace (no_trace ()) traces

let tclAgregateTraceList (tacs: trace tactic list): trace tactic =
  List.fold_left 
    (
      fun tac1 tac2 ->
        tac1 >>= fun trace1 ->
        tac2 >>= fun trace2 -> 
        tclUNIT @@ agregateTrace trace1 trace2
    ) 
    (tclUNIT @@ no_trace ()) 
    tacs

let catchable_exception = function
  | Logic_monad.Exception _ -> false
  | e -> CErrors.noncritical e

let goal_enter (f: Goal.t -> 'a tactic) =
  Proofview_monad.InfoL.tag (Proofview_monad.Info.Dispatch) begin
    iter_goal
      begin fun goal ->
        Env.get >>= fun env ->
        tclEVARMAP >>= fun sigma ->
        try f (gmake env sigma goal)
        with e when catchable_exception e ->
          let (e, info) = Exninfo.capture e in
          tclZERO ~info e
      end
  end

(**
  Tries the first tactic that does not fail in a list of tactics
*)
let rec tclFirst: 'a tactic list -> 'a tactic = function
  | [] ->
    let info = Exninfo.reify () in
    tclZERO ~info SearchBound
  | t::rest -> tclORELSE t (fun _ -> tclFirst rest)

let tclOrElse0 (tac1: trace tactic) (tac2: trace tactic): trace tactic =
  begin
    tclINDEPENDENTL @@ tclORELSE tac1 (fun _ -> tac2)
  end >>= fun traces -> tclUNIT @@ agregateTraceList traces

  let tclLOG (_: trace) (pp: Environ.env -> Evd.evar_map -> Pp.t * Pp.t) (tac: trace tactic) (must_use: Pp.t list) (forbidden: Pp.t list): trace tactic =
    let pr_trace_atom (env: Environ.env) (sigma: Evd.evar_map) ((is_success, d, hint, src): trace_atom): t =
      str (String.make d ' ') ++ str (if is_success then "✓" else "×") ++ spc () ++ hint ++ str " in (" ++ src ++ str ")." in
    Proofview.(
      tac >>= fun trace ->
      tclIFCATCH (
        tclENV >>= fun env ->
        tclEVARMAP >>= fun sigma ->
        Feedback.msg_notice (int @@ List.length trace.trace);
        Feedback.msg_notice (str "Trace:");
        Feedback.msg_notice (prlist_with_sep fnl (pr_trace_atom env sigma) trace.trace);
        let (hint, src) = pp env sigma in
        tclUNIT {trace with trace = (true, trace.current_depth, hint, src) :: trace.trace }
      ) tclUNIT (fun (exn,info) ->
          tclENV >>= fun env ->
          tclEVARMAP >>= fun sigma ->
          Feedback.msg_notice (int 1);
          pr_trace env sigma trace;
          (* let (hint, src) = pp env sigma in
          trace.trace := (false, trace.current_depth, hint, src) :: !(trace.trace); *)
          tclZERO ~info exn
      )
    )

(**
  Prints "idtac" if the [log] field is [true]
*)
let pr_info_nop (trace: trace) = if trace.log then Feedback.msg_notice (str "idtac.") else ()

(** 
  Prints a debug header if [log] is [true]
*)
let pr_dbg_header (trace: trace) = if trace.log then Feedback.msg_notice (str "(* info wauto: *)") else ()

(**
  Tries the given tactic and calls an info printer if it fails
*)
let tcl_try_dbg (debug_header_printer : trace -> unit) (tac: trace tactic): trace tactic =
  tac >>= fun trace ->
    begin
      tclOrElse0
        begin
          debug_header_printer trace;
          tclENV >>= fun env ->
          tclEVARMAP >>= fun sigma ->
            begin
              pr_trace env sigma trace;
              tclUNIT trace
            end
        end
        begin
          pr_info_nop trace;
          tclUNIT trace
        end
    end

(**
  Creates a function that takes a hint database and returns a hint list
*)
let hintmap_of (env: Environ.env) (sigma: Evd.evar_map) (secvars: Id.Pred.t) (concl: Evd.econstr): hint_db -> FullHint.t list =
  let hdc = try Some (decompose_app_bound sigma concl) with Bound -> None in
  match hdc with
  | None -> Hint_db.map_none ~secvars
  | Some hdc ->
      if occur_existential sigma concl then (fun db -> 
        match Hint_db.map_eauto env sigma ~secvars hdc concl db with
          | ModeMatch (_, l) -> l
          | ModeMismatch -> []
      )
      else Hint_db.map_auto env sigma ~secvars hdc concl

(**
  Returns a logged [intro] tactic
*)
let dbg_intro (trace: trace): trace tactic =
  tclLOG (no_trace ()) (fun _ _ -> (str "intro", str "")) (tclTHEN intro @@ tclUNIT trace) [] [] >>= fun trace ->
  Feedback.msg_notice (str "intro " ++ (int @@ List.length trace.trace));
  (goal_enter @@ fun goal -> tclUNIT trace) >>= fun new_trace -> Feedback.msg_notice (int @@ List.length new_trace.trace);
  tclUNIT trace

(**
  Returns a logged [assumption] tactic
*)
let dbg_assumption (trace: trace): trace tactic =
  tclLOG (no_trace ()) (fun _ _ -> (str "assumption", str "")) (tclTHEN assumption @@ tclUNIT trace) [] [] >>= fun trace ->
  Feedback.msg_notice (str "assumption " ++ (int @@ List.length trace.trace));
  tclUNIT trace

(**
  Returns a tactic that apply intro then try to solve the goal
*)
let intro_register (trace: trace) (kont: hint_db -> trace tactic) (db: hint_db): trace tactic =
  let nthDecl m gl =
    let hyps = Proofview.Goal.hyps gl in
    try
      List.nth hyps (m-1)
    with Failure _ -> CErrors.user_err Pp.(str "No such assumption.")
  in dbg_intro trace >>= fun trace ->
    goal_enter begin fun gl ->
      let extend_local_db decl db =
        let env = Goal.env gl in
        let sigma = Goal.sigma gl in
        push_resolve_hyp env sigma (Context.Named.Declaration.get_id decl) db
      in goal_enter @@ fun goal -> tclUNIT (nthDecl 1 goal) >>= (fun decl -> kont (extend_local_db decl db))
    end

let rec trivial_fail_db (trace: trace) (db_list: hint_db list) (local_db: hint_db) (must_use: Pp.t list) (forbidden: Pp.t list): trace tactic =
  begin
    tclINDEPENDENTL @@
      tclOrElse0 (dbg_assumption trace) @@
      tclOrElse0 (intro_register trace (fun db -> trivial_fail_db trace db_list db must_use forbidden) local_db) @@
      goal_enter begin fun gl ->
        let env = Goal.env gl in
        let sigma = Goal.sigma gl in
        let concl = Goal.concl gl in
        let secvars = compute_secvars gl in
        let hintmap = hintmap_of env sigma secvars concl in
        let hinttac = tac_of_hint trace db_list local_db concl must_use forbidden in
        (local_db::db_list)
          |> List.map_append (fun db -> try hintmap db with Not_found -> [])
          |> List.filter_map begin fun h ->
              if Int.equal (FullHint.priority h) 0 then
                Some (
                  (hinttac h) >>= fun trace ->
                    begin
                      tclINDEPENDENT
                        begin
                          let info = Exninfo.reify () in
                          tclZERO ~info SearchBound
                        end  <*> tclUNIT trace
                    end
                )
              else None
            end
          |> tclFirst
      end
  end >>= fun traces -> tclUNIT (agregateTraceList traces)

(**
  Returns a function that converts hints into tactics
*)
and tac_of_hint (trace: trace) (db_list: hint_db list) (local_db: hint_db) (concl: Evd.econstr) (must_use: Pp.t list) (forbidden: Pp.t list): FullHint.t -> trace tactic =
  let tactic: hint hint_ast -> trace tactic = function
    | Res_pf h -> tclTHEN (unify_resolve_nodelta h) (tclUNIT trace)
    | ERes_pf _ -> goal_enter (fun gl ->
        let info = Exninfo.reify () in
        Tacticals.tclZEROMSG ~info (str "eres_pf"))
    | Give_exact h  -> tclTHEN (exact h) (tclUNIT trace)
    | Res_pf_THEN_trivial_fail h ->
      tclTHEN
        (unify_resolve_nodelta h)
        (trivial_fail_db trace db_list local_db must_use forbidden)
    | Unfold_nth c ->
      goal_enter begin fun gl ->
       if exists_evaluable_reference (Goal.env gl) c then
          tclTHEN
            (Tacticals.tclPROGRESS (reduce (Genredexpr.Unfold [Locus.AllOccurrences,c]) Locusops.onConcl)) @@
            tclUNIT trace
       else
         let info = Exninfo.reify () in
         Tacticals.tclFAIL ~info (str"Unbound reference")
       end
    | Extern (p, tacast) ->
      tclTHEN
        (conclPattern concl p tacast) @@
        tclUNIT trace
  in
  let pr_hint (h: FullHint.t) (env: Environ.env) (sigma: Evd.evar_map): t * t =
    let origin = match FullHint.database h with
    | None -> mt ()
    | Some n -> str n
    in
    (Proofutils.pr_hint env sigma h, origin)
  in
  fun h -> tclLOG (no_trace ()) (pr_hint h) (FullHint.run h tactic) must_use forbidden

(**
  Searches a sequence of at most [n] tactics within [db_list] and [lems] that solves the goal

  The goal cannot contain evars
*)
let search (trace: trace) (n: int) (db_list: hint_db list) (lems: Tactypes.delayed_open_constr list) (must_use: Pp.t list) (forbidden: Pp.t list): trace tactic =
  let make_local_db (gl: Goal.t): hint_db =
    let env = Goal.env gl in
    let sigma = Goal.sigma gl in
    make_local_hint_db env sigma false lems
  in
  let rec search (trace: trace) (n: int) (local_db: hint_db): trace tactic =
    if Int.equal n 0 then
      let info = Exninfo.reify () in
      tclZERO ~info SearchBound
    else
      begin
        tclOrElse0 (dbg_assumption trace) @@
        tclOrElse0 (intro_register trace (fun db -> search trace n db) local_db) @@
        goal_enter begin fun gl ->
          let env = Goal.env gl in
          let sigma = Goal.sigma gl in
          let concl = Goal.concl gl in
          let hyps = Goal.hyps gl in
          let new_trace = incr_trace_depth trace in
          let secvars = compute_secvars gl in
          let hintmap = hintmap_of env sigma secvars  concl in
          let hinttac = tac_of_hint trace db_list local_db concl must_use forbidden in
          let tac: trace tactic list = (local_db::db_list)
            |> List.map_append (fun db -> try hintmap db with Not_found -> [])
            |> List.map 
              begin fun h ->
                tclAgregateTraceList [
                  (hinttac h);
                  goal_enter
                    begin fun gl ->
                      let hyps' = Goal.hyps gl in
                      let local_db' =
                        if hyps' == hyps then local_db else make_local_db gl
                      in
                      search new_trace (n-1) local_db'
                    end
                ]
              end
          in (tclFirst tac)
        end
      end
  in
  goal_enter begin fun gl ->
    let local_db = make_local_db gl in
    search trace n local_db
  end

(** 
  Generates the {! wauto} and {! rwauto} function
*)
let gen_wauto (info: bool) ?(n: int = 5) (lems: Tactypes.delayed_open_constr list) (dbnames: hint_db_name list option) (must_use: Pp.t list) (forbidden: Pp.t list): trace tactic =
  Hints.wrap_hint_warning @@
    goal_enter begin fun gl ->
    let db_list =
      match dbnames with
        | Some dbnames -> make_db_list dbnames
        | None -> current_pure_db ()
    in
    wrap_hint_warning @@  tcl_try_dbg pr_dbg_header @@ search (new_trace info) n db_list lems must_use forbidden
  end

(**
  Waterproof auto

  This function is a rewrite around coq-core.Auto.auto with the same arguments to be able to retrieve which tactics have been used in case of success.

  Returns a typed tactic containing the full trace
*)
let wauto (info: bool) (n: int) (lems: Tactypes.delayed_open_constr list) (dbnames: hint_db_name list): trace tactic = 
  gen_wauto info ~n lems (Some dbnames) [] []

(**
  Restricted Waterproof auto

  This function acts the same as {! wauto} but will fail if all proof found contain at least one must-use lemma that is unused or one hint that is in the [forbidden] list.
*)
let rwauto (info: bool) (n: int) (lems: Tactypes.delayed_open_constr list) (dbnames: hint_db_name list) (must_use: Pp.t list) (forbidden: Pp.t list): trace tactic =
  gen_wauto info ~n lems (Some dbnames) must_use forbidden
