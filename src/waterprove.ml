open Constr
open EConstr
open Pp
open Proofview

open Exceptions

(**
  List of forbidden inductive types
*)
let forbidden_inductive_types: string list = [
  "Coq.Init.Logic.all"; (* forall (should not be necessary) *)
  "Coq.Init.Logic.and"; (* /\ *)
  "Coq.Init.Logic.ex"; (* exists *)
  "Coq.Init.Logic.ex2"; (* exists2 *) 
  "Coq.Init.Logic.or"; (* \/ *)
]

(**
  Returns a [bool] from a [EConstr.constr] indicating if this term is forbidden in automation.

  Forbidden patterns: [forall _, _], [exists _, _], [_ /\ _] and [_ \/ _]
*)
let rec is_forbidden (sigma: Evd.evar_map) (term: constr): bool =
  let exists_in_array (term_array: constr array): bool = Array.exists (fun term -> is_forbidden sigma term) term_array in
  match kind sigma term with
    | Prod (binder, _, _) -> Names.Name.print binder.binder_name <> str "_"
    | Cast (sub_term, _, _) -> is_forbidden sigma sub_term
    | Lambda (_, _, right_side) -> is_forbidden sigma right_side
    | LetIn (_, value, _, right_side) -> is_forbidden sigma value || is_forbidden sigma right_side
    | App (f, args) -> is_forbidden sigma f || exists_in_array args
    | Case (_, _, params, _, _, c, branches) ->
      is_forbidden sigma c || exists_in_array params || Array.exists (fun (_, branch) -> is_forbidden sigma branch) branches
    | Fix (_, (_, _, bodies)) | CoFix (_, (_, _, bodies)) -> exists_in_array bodies
    | Proj (_, sub_term) -> is_forbidden sigma sub_term
    | Array (_, vals, def, _) -> is_forbidden sigma def || exists_in_array vals
    | Ind ((name, _), _) -> (* [exists], [/\], [\/], ... are defined by inductive types so they are caught here *)
      List.mem (Names.MutInd.print name) @@ List.map str forbidden_inductive_types
    | _ -> false

(**
  Tests that the current goal is not forbidden with the shield on.
*)
let shield_test (): unit tactic =
  Proofview.Goal.enter @@ fun goal ->
    begin
      let sigma = Proofview.Goal.sigma goal in
      let conclusion = Proofview.Goal.concl goal in
      if is_forbidden sigma conclusion then throw (FailedTest "shield");
      tclUNIT ()
    end

(**
  Waterprove

  This function is the main automatic solver of coq-waterproof.

  The databases used for the proof search are the one declared in the current imported dataset (see {! Hint_dataset.loaded_hint_dataset}).

  The forbidden patterns are defined in {! is_forbidden}.

  Arguments:
    - [depth] (int): max depth of the proof search
    - [shield] (bool): if set to [true], will stop the proof search if a forbidden pattern is found
    - [lems] (Tactypes.delayed_open_constr list): additional lemmas that are given to solve the proof
*)
let waterprove (depth: int) ?(shield: bool = false) (lems: Tactypes.delayed_open_constr list): unit tactic =
  Proofview.Goal.enter @@ fun goal ->
    begin
      let env = Proofview.Goal.env goal in
      let sigma = Proofview.Goal.sigma goal in
      let conclusion = Proofview.Goal.concl goal in
      Feedback.msg_notice (Printer.pr_etype_env env sigma conclusion);
      if is_forbidden sigma conclusion then throw (FailedAutomation "Coucou");
      tclUNIT ()
    end
