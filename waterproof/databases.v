(** # **Databases**

Authors: 
    - Adrian Vramulet (1284487)
    - Tudor Voicu (1339532)
    - Lulof Pirée (1363638)
    - Cosmin Manea (1298542)
Creation date: 14 June 2021

In this file, we construct so-called Hint Databases.
These databases can be used in combination with the tactics 
`auto` and `eauto`.
When using such a tactic, 
the hints in the database are recursively called 
until a certain search depth (standard is 5).
We choose to split the interesting hints among a number 
of different databases, so that the recursive search
size and the corresponding search time remain relatively small.

## **Equality**
We first look at databases that can be used for solving equalities, 
like $x + y = y + x$ and $|(\left|\log(e^x)|)\right| = |x|$.
The most important operation in each of the databases is the 
`reflexivity` tactic, since with that tactic, we want to solve the step.
We distinguish a number of operations and characteristics, 
and initialise these databases by adding a reflexivity hint.

--------------------------------------------------------------------------------

This file is part of Waterproof-lib.

Waterproof-lib is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

Waterproof-lib is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with Waterproof-lib.  If not, see <https://www.gnu.org/licenses/>.
*)


Require Import Coq.Logic.PropExtensionality.
Require Import Waterproof.definitions.set_definitions.
Require Import Waterproof.notations.notations.
Require Import Reals.
Require Import Reals.ROrderedType.
Require Import Coq.micromega.Lra.

(** ### **Additional ***)
Lemma base_same : forall C : Type,
    forall P : C -> Prop,
    forall x y : sig P, proj1_sig x = proj1_sig y -> x = y.
Proof.
intros C P x y H.
apply eq_sig_hprop.
intros.
apply proof_irrelevance.
apply H.
Qed.

Lemma same_base : forall C : Type,
    forall P : C -> Prop,
        forall x y : sig P, x = y -> proj1_sig x = proj1_sig y.
Proof.
intros C P x y H.
rewrite H.
trivial.
Qed.

Global Hint Resolve base_same : additional.
Global Hint Resolve same_base : additional.

Lemma Req_true : forall x y : R, x = y -> Reqb x y = true.
Proof.
intros. destruct (Reqb_eq x y). apply (H1 H).
Qed.

Lemma true_Req : forall x y : R, Reqb x y = true -> x = y.
Proof.
intros. destruct (Reqb_eq x y). apply (H0 H).
Qed.

Lemma Req_false : forall x y : R, x <> y -> Reqb x y = false.
Proof.
intros. unfold Reqb. destruct Req_dec. contradiction. trivial.
Qed.

Lemma false_Req : forall x y : R, Reqb x y = false -> x <> y.
Proof.
intros. destruct (Req_dec x y). rewrite (Req_true x y e) in H. 
assert (H1 : true <> false). auto with *. contradiction.
apply n.
Qed.

Global Hint Resolve (eq_sym) : reals.
Global Hint Resolve false_Req : reals.
Global Hint Resolve true_Req : reals.

(** ** Subsets*)
Lemma subset_elements_satisfy_predicate :
    forall V : subsets_R,
        forall x : V, 
            Waterproof.definitions.set_definitions.is_in V x.
Proof.
intro V.
induction x.
assumption.
Qed.
Global Hint Resolve subset_elements_satisfy_predicate : additional.

Lemma elements_satisfy_other_pred :
    ∀ (A : subsets_R) (pred : ℝ → Prop),
        (∀ a : A, pred a) ⇒
            ∀ b : ℝ, 
            Waterproof.definitions.set_definitions.is_in 
                A b ⇒ pred b.
    
        
Proof.
intros A pred A_satisfies b b_in_A.
set (c := (mk_element_R 
    (Waterproof.definitions.set_definitions.is_in A) b b_in_A)).
assert (pred_c : (pred c)) by eauto using A_satisfies with *.
eauto with *.
Qed.
(** 
### Intervals*)
Definition int_cc_prop {x y : R} :
    forall r : [x, y], x <= r <= y
    := subset_elements_satisfy_predicate [x,y].
Definition int_co_prop {x y : R} :
    forall r : [x, y), x <= r < y
    := subset_elements_satisfy_predicate [x,y).
Definition int_oc_prop {x y : R}:
    forall r : (x, y], x < r <= y
    := subset_elements_satisfy_predicate (x,y].
Definition int_oo_prop {x y : R}:
    forall r : (x, y), x < r < y
    := subset_elements_satisfy_predicate (x,y).
Definition int_cc_prop1 {x y : R} : forall r : [x,y], x <= r.
    intro r. 
    apply (subset_elements_satisfy_predicate [x,y]).
Qed.
Definition int_cc_prop2 {x y : R} : forall r : [x, y], r <= y.
    intro r.
    apply (subset_elements_satisfy_predicate [x,y]).
Qed.
Definition int_co_prop1 {x y : R} : forall r : [x,y), x <= r.
    intro r.
    apply (subset_elements_satisfy_predicate [x,y)).
Qed.
Definition int_co_prop2 {x y : R} : forall r : [x,y), r < y.
    intro r.
    apply (subset_elements_satisfy_predicate [x,y)).
Qed.
Definition int_oc_prop1 {x y : R} : forall r : (x,y], x < r.
    intro r.
    apply (subset_elements_satisfy_predicate (x,y]).
Qed.
Definition int_oc_prop2 {x y : R} : forall r : (x,y], r <= y.
    intro r.
    apply (subset_elements_satisfy_predicate (x,y]).
Qed.
Definition int_oo_prop1 {x y : R} : forall r : (x,y), x < r.
    intro r.
    apply (subset_elements_satisfy_predicate (x,y)).
Qed.
Definition int_oo_prop2 {x y : R} : forall r : (x,y), r < y.
    intro r.
    apply (subset_elements_satisfy_predicate (x,y)).
Qed.
Global Hint Resolve int_cc_prop : additional.
Global Hint Resolve int_co_prop : additional.
Global Hint Resolve int_oc_prop : additional.
Global Hint Resolve int_oo_prop : additional.

Global Hint Resolve int_cc_prop1 : additional.
Global Hint Resolve int_cc_prop2 : additional.
Global Hint Resolve int_co_prop1 : additional.
Global Hint Resolve int_co_prop2 : additional.
Global Hint Resolve int_oc_prop1 : additional.
Global Hint Resolve int_oc_prop2 : additional.
Global Hint Resolve int_oo_prop1 : additional.
Global Hint Resolve int_oo_prop2 : additional.
(** ## Absolute values and inverses*)
Lemma div_sign_flip : forall r1 r2 : R, r1 > 0 -> r2 > 0 -> r1 > 1 / r2 -> 1 / r1 < r2.
Proof.
intros.
unfold Rdiv in *.
rewrite Rmult_1_l in *.
rewrite <- (Rinv_involutive r2).
apply (Rinv_lt_contravar (/ r2) r1).
apply Rmult_lt_0_compat. apply Rinv_0_lt_compat. apply H0. apply H.
apply H1. apply Rgt_not_eq. apply H0.
Qed.

Lemma div_pos : forall r1 r2 : R, r1 > 0 ->1 / r1 > 0.
Proof.
intros. unfold Rdiv. rewrite Rmult_1_l. apply Rinv_0_lt_compat. apply H.
Qed.

Lemma Rabs_zero : forall r : R, Rabs (r - 0) = Rabs r.
Proof.
intros. rewrite Rminus_0_r. trivial.
Qed.

Lemma inv_remove : forall r1 r2 : R, 0 < r1 -> 0 < r2 -> 1 / r1 < 1 / r2 -> r1 > r2.
Proof.
intros.
unfold Rdiv in *. rewrite Rmult_1_l in *.
rewrite <- (Rinv_involutive r1), <- (Rinv_involutive r2).
apply (Rinv_lt_contravar (/ r1) (/ r2)). apply Rmult_lt_0_compat. apply Rinv_0_lt_compat. apply H.
apply Rinv_0_lt_compat. apply H0. rewrite Rmult_1_l in *. apply H1.
all: apply Rgt_not_eq; assumption.
Qed.

Lemma Rle_abs_min : forall x : R, -x <= Rabs x.
Proof.
intros. rewrite <- (Rabs_Ropp (x)). apply Rle_abs.
Qed.

Lemma Rge_min_abs : forall x : R, x >= -Rabs x.
Proof.
intros. rewrite <- (Ropp_involutive x). apply Ropp_le_ge_contravar.
rewrite (Rabs_Ropp (- x)). apply Rle_abs.
Qed.

Lemma Rmax_abs : forall a b : R, Rmax (Rabs a) (Rabs b) >= 0.
Proof.
intros.
apply (Rge_trans _ (Rabs a) _).
apply Rle_ge.
apply Rmax_l.
apply (Rle_ge 0 (Rabs a)).
apply Rabs_pos.
Qed.


Global Hint Resolve div_sign_flip : reals.
Global Hint Resolve div_pos : reals.
Global Hint Resolve inv_remove : reals.
Global Hint Resolve Rabs_left : reals.
Global Hint Resolve Rabs_right : reals.
Global Hint Resolve Rabs_left1 : reals.
Global Hint Resolve Rabs_pos_lt : reals.
Global Hint Resolve Rabs_zero : reals.
Global Hint Resolve Rle_abs : reals.
Global Hint Resolve Rabs_pos : reals.
Global Hint Resolve Rle_abs_min : reals.
Global Hint Resolve Rge_min_abs : reals.
Global Hint Resolve Rmax_abs : reals.


Hint Extern 1 => rewrite Rabs_zero : reals.
(** ## Subsequences*)



Require Import Reals.
Local Open Scope R_scope.
From Ltac2 Require Import Ltac2 Ident.
Require Import Ltac.
Require Import Ltac2.Init.


Hint Extern 0 => reflexivity : 
  eq_opp eq_zero eq_one
  eq_abs eq_sqr eq_exp eq_other 
  eq_plus eq_minus eq_mult.

Hint Extern 1 (_ = _) => lra :
  
  eq_abs eq_sqr eq_exp.

(** Next, we will categorise existing lemmas of the form `forall _ : R, _ = _`, and use the rewrite tactic to change the goal.
These are ideal for solving equalities, since they do not require any assumptions.

Note that we add all lemmas to a general database ``.*)
(** ### **Plus, minus and multiplication rewriters**
In this database, we will add commutative, associative and distributative properties of numbers in combination with the $+$ operator.
We let $x, y ∈ \mathbb{R}$.

#### Commutativity:
We have the following commutative properties:*)
Hint Extern 1 => (rewrite Rplus_comm) :  eq_plus. (* x + y = y + x *)
Hint Extern 1 => (rewrite Rmult_comm) :  eq_mult. (* x * y = y * x *)
(** #### Associativity
We have the following associative properties:*)
Hint Extern 1 => (rewrite Rplus_assoc) :  eq_plus. (* x + y + z = x + (y + z) *)
Hint Extern 1 => (rewrite Rmult_assoc) :  eq_mult. (* x * y * z = x * (y * z) *)
(** #### Distributivity
We have the following distributive properties:*)
Hint Extern 1 => (rewrite Rdiv_plus_distr) :  eq_plus. 
  (* (x + y) / z = x / z + y / z *)
Hint Extern 1 => (rewrite Rdiv_minus_distr) :  eq_minus. 
  (* (x - y) / z = x / z - y / z *)
Hint Extern 1 => (rewrite Rmult_plus_distr_l) :  eq_mult eq_plus. 
  (* x * (y+z) = x * y + x * z *)
Hint Extern 1 => (rewrite Rmult_plus_distr_r) :  eq_mult eq_plus. 
  (* (x+y) * z = x * z + y * z *)
(** #### Other
We have some other properties:
*)
Hint Extern 1 => (unfold Rminus) : eq_minus.
(** ### **Opposite rewriters**
In this database, we will add properties with the additive inverse.*)
(** #### Distributitivity
We have the following distributive properties containing additive inverses:*)
Hint Extern 1 => (rewrite Ropp_minus_distr) :  eq_opp. 
  (* - (x - y) = y - x *)
Hint Extern 1 => (rewrite Ropp_minus_distr') :  eq_opp. 
  (* - (y - x) = x - y *)
Hint Extern 1 => (rewrite Ropp_mult_distr_l) :  eq_opp. 
  (* - (x * y) = - x * y *)
Hint Extern 1 => (rewrite Ropp_mult_distr_r) :  eq_opp.
  (* - (x * y) = x * - y *)
Hint Extern 1 => (rewrite Ropp_mult_distr_l_reverse) :  eq_opp. 
  (* - x * y = - (x * y) *)
Hint Extern 1 => (rewrite Ropp_mult_distr_r_reverse) :  eq_opp. 
  (* x * - y = - (x * y) *)
Hint Extern 1 => (rewrite Ropp_plus_distr) :  eq_opp. 
  (* - (x + y) = - x + - y. *)
(** #### Other 
We have some other properties:*)
Hint Extern 1 => (rewrite Ropp_involutive) :  eq_opp. (* --a = a *)
Hint Extern 1 => (rewrite Rmult_opp_opp) :  eq_opp. (* -a * -b = a * b *)
Hint Extern 1 => (rewrite Ropp_div) :  eq_opp. (* - a / b = - (a / b) *)
Hint Extern 1 => (rewrite Rplus_opp_l) :  eq_opp. (* -a  + a = 0 *)
Hint Extern 1 => (rewrite Rplus_opp_r) :  eq_opp. (* a  + -a = 0 *)
(** ### **Simple number arithmetic**
Addition with 0 and multiplication with 0 or 1 is a trivial task, so we use two databases to resolve such simple steps.

#### Arithmetic with 0's
We have the following properties for equations with 0:*)
Hint Extern 1 => (rewrite Rplus_0_l) :  eq_zero. (* 0 + x = x *)
Hint Extern 1 => (rewrite Rplus_0_r) :  eq_zero. (* x + 0 = x *)
Hint Extern 1 => (rewrite Rminus_0_l) :  eq_zero. (* 0 - x = - x *)
Hint Extern 1 => (rewrite Rminus_0_r) :  eq_zero. (* x - 0 = x *)
Hint Extern 1 => (rewrite Rmult_0_l) :  eq_zero. (* 0 * x = 0 *)
Hint Extern 1 => (rewrite Rmult_0_r) :  eq_zero. (* x * 0 = 0 *)
Hint Extern 1 => (rewrite pow_O) :  eq_zero. (* x ^ 0 = 1 *)
(** #### Arithmetic with 1's
We have the following properties for equations with 1:*)
Hint Extern 1 => (rewrite Rmult_1_l) :  eq_one. (* 1 * x = x *)
Hint Extern 1 => (rewrite Rmult_1_r) :  eq_one. (* x * 1 = x *)
Hint Extern 1 => (rewrite Rinv_1) :  eq_one. (* x / 1 = x *)
Hint Extern 1 => (rewrite pow_1) :  eq_one. (* x ^ 1 = x *)
Hint Extern 1 => (rewrite Rinv_involutive) : eq_one. (* / / x = x *)
(** ### **Distances and absolute values**
There are a number of trivial steps regarding distances, or absolute values.

#### Distance (R_dist)
We have the following properties:*)
Hint Extern 1 => (rewrite R_dist_eq) :  eq_abs. 
  (* ||a - a|| = 0 *)
Hint Extern 1 => (rewrite R_dist_mult_l) :  eq_abs. 
  (* ||a * b - a * c|| = ||a|| * ||b - c|| *)
Hint Extern 1 => (rewrite R_dist_sym) :  eq_abs. 
  (*||a - b|| = ||b - a||*)
(** #### Absolute value (Rabs)
We have the following properties:*)
Hint Extern 1 => (rewrite Rabs_minus_sym) :  eq_abs. 
  (* |a - b| = |b - a|, using Rabs *)
Hint Extern 1 => (rewrite Rabs_Rabsolu) :  eq_abs. 
  (* | |a| | = |a| *)
Hint Extern 1 => (rewrite Rabs_Ropp) :  eq_abs. 
  (* |-a| = |a| *)
Hint Extern 1 => (rewrite Rabs_mult) :  eq_abs. 
  (* |a * b| = |a| * |b| *)
Hint Extern 1 => (rewrite Rsqr_abs) :  eq_abs. 
  (* a^2 = |a|^2 *)
Hint Extern 1 => (rewrite sqrt_Rsqr_abs) :  eq_abs. 
  (* sqrt(a^2) = |a| *)
Hint Extern 1 => (rewrite pow2_abs) :  eq_abs. 
  (* | a |^2 = a^2*)
(** ### **Squares**
There are a number of trivial steps regarding squares.
We have the following properties:*)
Hint Extern 1 => (rewrite Rsqr_pow2) :  eq_sqr. (* a² = a ^ 2 *)
Hint Extern 1 => (rewrite Rsqr_plus) :  eq_sqr. (* (a-b)² = a² + b² + 2*a*b *)
Hint Extern 1 => (rewrite Rsqr_plus_minus) :  eq_sqr. (* (a+b)*(a-b) = a² - b² *)
Hint Extern 1 => (rewrite Rsqr_minus) :  eq_sqr. (* (a-b)² = a² + b² - 2*a*b *)
Hint Extern 1 => (rewrite Rsqr_minus_plus) :  eq_sqr. (* (a-b)*(a+b) = a² - b² *)
Hint Extern 1 => (rewrite Rsqr_neg) :  eq_sqr. (* a² = (-a)² *)
Hint Extern 1 => (rewrite Rsqr_neg_minus) :  eq_sqr. (* (a-b)² = (b-a)² *)
Hint Extern 1 => (rewrite Rsqr_mult) :  eq_sqr. (* (a*b)² = a² * b² *)
(** ### **Exponentials**
There are a number of trivial steps regarding exponentials. We have the following properties:*)
Hint Extern 1 => (rewrite ln_exp) :  eq_exp. (* ln (exp a)) = a *)
Hint Extern 1 => (rewrite exp_Ropp) :  eq_exp. (* exp (-a) = / exp a*)
Hint Extern 1 => (rewrite exp_plus) :  eq_exp. (* exp(a+b) = exp(a) * exp(b) *)
Hint Extern 1 => (rewrite ln_exp) :  eq_exp. (* ln (exp a)) = a *)









