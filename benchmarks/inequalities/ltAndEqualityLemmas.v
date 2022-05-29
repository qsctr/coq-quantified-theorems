Require Import Coq.Arith.Lt.
Require Import Nat Arith.

Inductive lst : Type :=
  | Nil : lst
  | Cons : nat -> lst -> lst.

Fixpoint len (l : lst) : nat :=
    match l with
    | Nil => 0
    | Cons x y => 1 + len y
    end.
  
Fixpoint append (l1 : lst) (l2 : lst) : lst :=
  match l1 with
  | Nil => l2
  | Cons x y => Cons x (append y l2)
  end.

Fixpoint rev (l1 : lst) : lst :=
    match l1 with
    | Nil => Nil
    | Cons x y => append (rev y) (Cons x Nil)
    end.

Fixpoint double double_arg0
    := match double_arg0 with
       | 0 => 0
       | S n => S (S (double n))
       end.


Lemma len_append : forall x y : lst, len (append x y) = plus (len x) (len y).
Proof.
    intros. induction x.
    - reflexivity.
    - simpl. rewrite IHx. reflexivity.
Qed.

Lemma appendToNil : forall l, len (append l Nil) = len l.
Proof.
   induction l.
   - reflexivity.
   - simpl. rewrite IHl. reflexivity.
Qed.

Lemma lenSCons : forall l1 l2 n, len (append l1 (Cons n l2)) = S (len (append l1 l2)).
Proof.
   induction l1.
   - intros. reflexivity.
   - intros. simpl. f_equal. apply IHl1.
Qed.

Theorem len_rev : forall x : lst, len (rev x) < S (len x).
Proof.
  intros.
  induction x.
  - simpl. apply lt_0_Sn.
  - simpl. rewrite len_append. simpl. rewrite plus_comm. simpl. apply lt_n_S. assumption.
Qed.

Theorem appLenS : forall x y, (len (append x y)) <  S (len (append y x)).
Proof.
  induction x.
  - intros. simpl. rewrite appendToNil. apply lt_n_Sn.
  - intros. simpl. apply lt_n_S. rewrite lenSCons. apply IHx.
Qed.

Theorem theorem0 : forall x, (len (append x x)) < S (double (len x)).
Proof.
  induction x.
  - simpl. apply lt_0_Sn.
  - simpl. apply lt_n_S. rewrite lenSCons. apply lt_n_S. assumption.
Qed.
