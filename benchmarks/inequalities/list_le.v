Require Import Arith.

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


Theorem consLT : forall l1 n, (len l1) <= (len (Cons n l1)).
Proof.
  induction l1.
  - intros. simpl. apply le_0_n.
  - intros. simpl. apply le_n_S. apply le_n_Sn.
Qed.

Theorem appendLT : forall l1 l2, (len l1) <= (len (append l1 l2)).
Proof.
    intros. induction l1.
    - simpl. apply le_0_n.
    - simpl. apply le_n_S. assumption.
Qed.

Theorem appendLT2 : forall l1 l2, (len l2) <= (len (append l1 l2)).
Proof.
    intros. induction l1.
    - simpl. apply le_refl.
    - simpl. apply (le_trans (len l2) (len (append l1 l2)) (S (len (append l1 l2)))). assumption.
      apply le_n_Sn.
Qed.

Lemma append_assoc: forall l1 l2 l3, append l1 (append l2 l3) = (append (append l1 l2) l3).
Admitted.

Lemma len_app_cons: forall l1 l2 n, len (append l1 (Cons n l2)) = S (len (append l1 l2)).
Admitted.

Theorem appendLT3 : forall l1 l2, (len l1) <= (len (append (rev l1) l2)).
Proof.
    induction l1.
    - intros. simpl. apply le_0_n.
    - intros. simpl. rewrite <- append_assoc. simpl. rewrite len_app_cons.
      apply le_n_S. apply IHl1.
Qed.