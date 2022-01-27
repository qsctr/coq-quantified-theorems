(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(*  ---                        two_power.v                             ---  *)
(*                                                                          *)
(* Author: Pierre Casteran.                                                 *)
(*    LABRI, URA CNRS 1304,                                                 *)
(*    Departement d'Informatique, Universite Bordeaux I,                    *)
(*    33405 Talence CEDEX,                                                  *)
(*    e-mail:  casteran@labri.u-bordeaux.fr                                 *)

(* From additions/two_power.v *)

Require Import Arith.

Fixpoint two_power (m : nat) : nat :=
  match m with
  | O => 1
  | S n => S (S 0) * two_power n
  end.

Lemma mult_le_l : forall a b c : nat, b <= c -> a * b <= a * c.
(******************************************)
Proof.
 simple induction a; simpl in |- *; [ auto with arith | intros ].
 apply plus_le_compat; auto with arith.
Qed.

Lemma mult_lt_l : forall a b c : nat, 0 < a -> b < c -> a * b < a * c.
(******************************************)
Proof.
 simple induction a.
 intros; absurd (0 < 0); auto with arith.
 intros; simpl in |- *.
 apply lt_le_trans with (c + n * b).
 rewrite (plus_comm b (n * b)); rewrite (plus_comm c (n * b));
  apply plus_lt_compat_l; auto with arith.
 apply plus_le_compat_l; auto with arith.
Qed.


Lemma mult_p_lt_qp : forall p q : nat, 0 < p -> S 0 < q -> p < q * p.
(************************************)
Proof.
 intros.
 rewrite mult_comm.
 pattern p at 1 in |- *; rewrite <- mult_1_r; apply mult_lt_l; assumption.
Qed.

Lemma zero_lt_pow : forall a : nat, 0 < two_power a.
(********************************************)
Proof.
  simple induction a.
  auto.
 intros.
 apply lt_plus_trans. auto.
Qed.


Lemma two_power_S : forall n : nat, two_power (S n) = two_power n * S (S 0).
(**************************************************)
Proof.
  intros.
  unfold two_power at 1. rewrite mult_comm. auto.
Qed.


Lemma two_power_S_lt : forall n : nat, two_power n < two_power (S n).
(***************************************************************)
Proof.
  intro. rewrite two_power_S.
  rewrite mult_comm.
  apply mult_p_lt_qp. apply zero_lt_pow.
  auto.
Qed.
