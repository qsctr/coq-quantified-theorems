Require Import Nat Arith.

Inductive INT : Type := zero : INT | succ : INT -> INT.

Fixpoint add (add_arg0 : INT) (add_arg1 : INT) : INT
           := match add_arg0, add_arg1 with
              | n, zero => n
              | n, succ m => succ (add n m)
              end.

Fixpoint mult (mult_arg0 : INT) (mult_arg1 : INT) : INT
           := match mult_arg0, mult_arg1 with
              | n, zero => zero
              | n, succ m => add n (mult n m)
              end.

Theorem mult_zero : forall (n : INT), mult zero n = mult n zero.
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem add_assoc : forall (x y z : INT), add (add x y) z = add x (add y z).
Proof.
  intros.
  induction z.
  - reflexivity.
  - simpl. rewrite IHz. reflexivity.
Qed.

Lemma add_zero : forall (x : INT), add zero x = x.
Proof.
  intros.
  induction x.
  - reflexivity.
  - simpl. rewrite IHx. reflexivity.
Qed.

Lemma add_succ : forall (x y : INT), add (succ x) y = succ (add x y).
Proof.
  intros.
  induction y.
  - reflexivity.
  - simpl. rewrite IHy. reflexivity.
Qed.

Theorem add_comm : forall (x y : INT), add x y = add y x.
Proof.
  intros.
  induction x.
  - rewrite add_zero. reflexivity.
  - simpl. rewrite add_succ. rewrite IHx. reflexivity.
Qed.

Theorem mult_succ : forall (n m : INT), mult (succ n) m = add m (mult n m).
Proof.
  intros.
  induction m.
  - reflexivity.
  - simpl. rewrite IHm. rewrite add_succ. rewrite add_succ. rewrite <- add_assoc. rewrite (add_comm n m). rewrite add_assoc. reflexivity.
Qed.

Theorem theorem0 : forall (n : INT) (m : INT), eq (mult n m) (mult m n).
Proof.
  intros.
  induction n.
  - rewrite mult_zero. reflexivity.
  - simpl. rewrite mult_succ. rewrite IHn. reflexivity.
Qed.

