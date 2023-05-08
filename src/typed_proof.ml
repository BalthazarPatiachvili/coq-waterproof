open Proofview
open Proofview_monad
open Proofview_monad.Logical

type goal = {
  env : Environ.env;
  sigma : Evd.evar_map;
  concl : EConstr.constr ;
  state : StateStore.t;
}

let env ({env; _}: goal): Environ.env = env
let sigma ({sigma; _}: goal): Evd.evar_map = sigma
let concl ({concl; _}: goal): EConstr.constr = concl

(* let iter_goal (i: goal -> 'a tactic) =
  Comb.get >>= fun initial ->
  Proofview_monad.Logical.List.fold_left begin fun (subgoals as cur) goal ->
    Solution.get >>= fun step ->
    match cleared_alias step goal with
    | None -> return cur
    | Some goal ->
        Comb.set [goal] >>
        i goal >>
        Proof.map (fun comb -> comb :: subgoals) Comb.get
  end [] initial >>= fun subgoals ->
  Solution.get >>= fun evd ->
  Comb.set CList.(undefined evd (flatten (rev subgoals))) *)

type 'a tactic = 'a Logical.t

let enter (f: goal -> 'a Logical.t): 'a Logical.t =
  let f gl = InfoL.tag (Info.DBranch) (f gl) in
  InfoL.tag (Info.Dispatch) begin
  iter_goal begin fun goal ->
    Env.get >>= fun env ->
    tclEVARMAP >>= fun sigma ->
    try f (gmake env sigma goal)
    with e when catchable_exception e ->
      let (e, info) = Exninfo.capture e in
      tclZERO ~info e
  end
  end