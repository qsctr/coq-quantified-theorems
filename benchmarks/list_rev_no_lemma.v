Require Import Nat Arith.

Inductive Lst : Type := nil : Lst | cons : nat -> Lst -> Lst.

Fixpoint append (append_arg0 : Lst) (append_arg1 : Lst) : Lst
           := match append_arg0, append_arg1 with
              | nil, x => x
              | cons x y, z => cons x (append y z)
              end.

Fixpoint rev (rev_arg0 : Lst) : Lst
           := match rev_arg0 with
              | nil => nil
              | cons x y => append (rev y) (cons x nil)
              end.

Theorem append_assoc : forall x y z : Lst, append (append x y) z = append x (append y z).
Proof.
  intros.
  induction x.
  - reflexivity.
  - simpl. rewrite IHx. reflexivity.
Qed.

Theorem rev_append_cons_aux : forall (l1 l2 : Lst) (x : nat), rev (append (rev l1) (cons x l2)) = append (rev l2) (cons x l1).
Proof.
  intro.
  induction l1.
  - reflexivity.
  - intros. simpl. rewrite append_assoc. simpl. rewrite IHl1. simpl. rewrite append_assoc. reflexivity.
Qed.

Theorem rev_append_cons : forall (l : Lst) (x : nat), rev (append (rev l) (cons x nil)) = cons x l.
Proof.
  intros.
  induction l.
  - reflexivity.
  - simpl. rewrite append_assoc. simpl. rewrite rev_append_cons_aux. reflexivity.
Qed.
