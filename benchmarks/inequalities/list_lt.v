Require Import Coq.Arith.Lt.

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

Theorem consLT : forall l1 n, (len l1) < (len (Cons n l1)).
Proof.
  induction l1.
  - intros. simpl. apply lt_0_Sn.
  - intros. simpl. apply lt_n_S. apply lt_n_Sn.
Qed.

Theorem appendLT : forall l1 l2 n, (len l1) < (len (append l1 (Cons n l2))).
Proof.
    intros. induction l1.
    - simpl. apply lt_0_Sn.
    - simpl. apply lt_n_S. assumption.
Qed.

