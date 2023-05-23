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

Require Import Waterproof.Waterproof.
Require Import Waterproof.Automation.
Require Import Waterproof.Waterprove.

Waterproof Clear Automation.

Goal 0 = 0.
Proof.
  Fail waterprove 5 false [] Positive.
Abort.

Goal forall x y: nat, forall f: nat -> nat, x = y -> f (S x) = f (S y).
Proof.
  Fail waterprove 5 false [] Positive.
Abort.