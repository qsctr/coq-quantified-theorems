Require Import Nat Arith.

Inductive Lst : Type := cons : nat -> Lst -> Lst |  nil : Lst.

Fixpoint append (append_arg0 : Lst) (append_arg1 : Lst) : Lst
           := match append_arg0, append_arg1 with
              | nil, x => x
              | cons x y, z => cons x (append y z)
              end.

Fixpoint len (len_arg0 : Lst) : nat
           := match len_arg0 with
              | nil => 0
              | cons x y => plus 1 (len y)
              end.

Theorem theorem0 : forall (x : Lst) (y : Lst), le (len (append x y)) (plus (len x) (len y)).
Proof.
   intros.
   induction x.
   - simpl. apply le_n_S. assumption.
   - simpl. apply le_refl.
Qed.


Theorem theorem1 : forall (x : Lst) (y : Lst), le (len x) (len (append x y)).
Proof.
   intros.
   induction x.
   - simpl. apply le_n_S. assumption.
   - simpl. apply le_0_n.
Qed.


Theorem theorem2 : forall (x : Lst) (y : Lst), le (len y) (len (append x y)).
Proof.
   intros.
   induction x.
   - simpl. apply Nat.le_le_succ_r. assumption.
   - simpl. apply le_refl.
Qed.


Theorem theorem3 : forall (x : Lst) n, (len x) < (len (append x (cons n nil))).
Proof.
   induction x.
   - intros. simpl. apply lt_n_S. apply IHx.
   - intros. simpl. apply Nat.lt_0_1.
Qed.


Theorem theorem4 : forall (x : Lst) n (y : Lst), (len x) < (len (append x (cons n y))).
Proof.
   induction x.
   - intros. simpl. apply lt_n_S. apply IHx.
   - intros. simpl. apply Nat.lt_0_succ.
Qed.