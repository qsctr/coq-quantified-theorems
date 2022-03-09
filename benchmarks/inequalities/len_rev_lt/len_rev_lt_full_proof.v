(* From lfind Require Import LFind. *)
Unset Printing Notations.
Set Printing Implicit.
Require Import Nat Arith.

Fixpoint plus (n1 : nat) (n2 : nat) : nat :=
  match n1 with
  | O => n2
  | S n1' => S (plus n1' n2)
  end.

Inductive lst : Type :=
  | Nil : lst
  | Cons : nat -> lst -> lst.

Fixpoint len (l : lst) : nat :=
  match l with
  | Nil => 0
  | Cons x y => plus 1 (len y)
  end.

Fixpoint append (l1 : lst) (l2 : lst) : lst :=
  match l1 with
  | Nil => l2
  | Cons x y => Cons x (append y l2)
  end.

Fixpoint rev (l : lst) : lst :=
  match l with
  | Nil => Nil
  | Cons x y => append (rev y) (Cons x Nil)
  end.

Lemma len_append : forall x y : lst, len (append x y) = plus (len x) (len y).
Admitted.


Theorem len_rev : forall x : lst, len (rev x) < S (len x).
Proof.
  intros.
  induction x.
  - simpl. apply le_refl.
  - simpl. rewrite len_append. simpl. rewrite plus_comm. simpl. apply lt_n_S. assumption.
Qed.

