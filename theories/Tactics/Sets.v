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

Require Import Ltac2.Ltac2.
Require Import Ltac2.Message.
Require Import Sets.Ensembles.
Require Import Sets.Classical_sets.

Require Import Tactics.Conclusion.
Require Import Util.Goals.

(**
  Destructs a statement regarding an element being contained in a union/intersection of two sets into its respective cases.

  Arguments:
    - no arguments.

  Does:
    - matches the goal with two possibilities: an element being contained in an intersection of sets or an element being contained in a union of sets.
    - in the first case, it just splits the goal into its respective subcases (i.e. the element being contained in every set in the intersecion).
    - in the second case, it just splits the goal into its respective subcases (i.e. the element being containined in one such set from the union), and then tries to solve the remaining of the proof.
*)
Ltac2 destruct_sets () :=
  lazy_match! goal with
    | [h : In _ (Intersection _ _ _) _ |- _ ] =>
      let h_val := Control.hyp h in
      destruct $h_val
    | [h : In _ (Union _ _ _) _ |- _ ] =>
      let h_val := Control.hyp h in
      destruct $h_val;
      try (check_and_solve (Control.goal ()) None); 
      try (ltac1:(solve [firstorder (auto with sets)]));
      try (ltac1:(solve [firstorder (eauto with sets)]))
  end.

(**
  Tries to prove a set inclusion.
    
  Arguments:
    - no arguments.
    
  Does:
    - calls the tactics/functions [intro], [intro], [destruct_sets], [contradiction] and various proof finishing functions, in this order, in order to automatically prove a set inclusion.
*)
Ltac2 trivial_set_inclusion () :=
  try (intro x);
  try (intro h);
  try (destruct_sets ());
  ltac1:(try contradiction);
  try (check_and_solve (Control.goal ()) None);
  try (ltac1:(solve [firstorder (auto with sets)]));
  try (ltac1:(solve [firstorder (eauto with sets)])).



(**
  Prove a trivial set equality.

  Arguments:
    - no arguments.

  Does:
    - calls the tactics/functions [intros], [intros], [apply Extensionality_Ensembles], [unfold Same_set], [unfold Included], [split], and twice [trivial_set_inclusion], in order to prove a set equality.
*)
Ltac2 trivial_set_equality () :=
  try (intros A);
  try (intros B);
  try (apply Extensionality_Ensembles);
  try (unfold Same_set); 
  try (unfold Included);
  try (split);
  try (split);
  try (trivial);
  try (split);
  try (trivial_set_inclusion ());
  try (trivial_set_inclusion ()).

Ltac2 Notation "This" "set" "equality" "is" "trivial" :=
  panic_if_goal_wrapped ();
  trivial_set_equality ().

(**
  Prove a set equality of the form A = B by proving that A is a subset of B and B is a subset of A.

  Arguments:
    - No arguments.

  Does:
    - Proves that A = B by proving that A is a subset of B and B is a subset of A.
*)
Ltac2 we_prove_equality_by_proving_two_inclusions () :=
  try (ltac1:(apply Extensionality_Ensembles));
  unfold Same_set;
  unfold Included;
  split.

Ltac2 Notation "We" "prove" "equality" "by" "proving" "two" "inclusions" :=
  panic_if_goal_wrapped ();
  we_prove_equality_by_proving_two_inclusions ().