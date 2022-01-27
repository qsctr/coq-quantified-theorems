Require Import Nat Arith Plus Minus.

Fixpoint mult (n m : nat) : nat :=
  match m with
  | S m' => n + mult n m'
  | 0 => 0
  end.

Lemma mult_0 : forall (x : nat), mult 0 x = 0.
Proof.
  intros.
  induction x.
  - reflexivity.
  - simpl. assumption.
Qed.

Lemma le_mult : forall (x y : nat), y <= mult (S x) y.
Proof.
  intros.
  induction y.
  - reflexivity.
  - simpl. apply le_n_S. rewrite plus_comm. apply le_plus_trans. assumption.
Qed.

Theorem theorem0 : forall (x : nat) (y : nat), eq (minus (mult x y) y) (mult (minus x 1) y).
Proof.
  intros.
  destruct x.
  - simpl. rewrite mult_0. reflexivity.
  - simpl. rewrite <- minus_n_O. induction y.
    + reflexivity.
    + simpl. rewrite <- IHy. symmetry. apply (plus_minus (x + mult (S x) y) y (x + (mult (S x) y - y))). rewrite plus_assoc. rewrite (plus_comm y x). rewrite <- plus_assoc. rewrite le_plus_minus_r.
      * reflexivity.
      * apply le_mult.
Qed.

Lemma mult_s : forall (n m : nat), mult (S n) m = m + mult n m.
Proof.
  intros.
  induction m.
  - reflexivity.
  - simpl. rewrite IHm. rewrite plus_assoc. rewrite (plus_comm n m). rewrite plus_assoc. reflexivity.
Qed.

Theorem theorem1 : forall (n : nat) (m : nat), eq (mult n m) (mult m n).
Proof.
  intros.
  induction m.
  - simpl. rewrite mult_0. reflexivity.
  - simpl. rewrite mult_s. rewrite IHm. reflexivity.
Qed.

