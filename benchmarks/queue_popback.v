Require Import Bool Nat Arith.

Inductive Lst : Type := nil : Lst | cons : nat -> Lst -> Lst.

Scheme Equality for Lst.

Inductive Queue : Type := queue : Lst -> Lst -> Queue.

Fixpoint len (len_arg0 : Lst) : nat
           := match len_arg0 with
              | nil => 0
              | cons x y => plus 1 (len y)
              end.

Definition qlen (qlen_arg0 : Queue) : nat
           := let 'queue x y := qlen_arg0 in
              plus (len x) (len y).

Fixpoint append (append_arg0 : Lst) (append_arg1 : Lst) : Lst
           := match append_arg0, append_arg1 with
              | nil, x => x
              | cons x y, z => cons x (append y z)
              end.

Fixpoint butlast (butlast_arg0 : Lst) : Lst
           := match butlast_arg0 with
              | nil => nil
              | cons n x => if Lst_beq x nil then nil else cons n (butlast x)
              end.

Definition qpopback (qpopback_arg0 : Queue) : Queue
           := match qpopback_arg0 with
              | queue x (cons n y) => queue x y
              | queue x nil => queue (butlast x) nil
              end.

Definition isAmortized (isAmortized_arg0 : Queue) : bool
           := let 'queue x y := isAmortized_arg0 in
              leb (len y) (len x).

Definition isEmpty (isEmpty_arg0 : Queue) : bool
           := let 'queue x y := isEmpty_arg0 in
              andb (Lst_beq x nil) (Lst_beq y nil).

Lemma len_butlast : forall (l : Lst) (n : nat), S (len (butlast (cons n l))) = len (cons n l).
Proof.
  intros.
  generalize dependent n.
  induction l.
  - reflexivity.
  - intros. simpl. simpl in IHl. rewrite IHl. reflexivity.
Qed.

Theorem theorem0 : forall (q : Queue) (n : nat), isAmortized q && negb (isEmpty q) = true -> eq (plus 1 (qlen (qpopback q))) (qlen q).
Proof.
  intros.
  destruct q.
  destruct l0.
  - simpl. rewrite <- plus_n_O. destruct l.
    + simpl in H. discriminate.
    + rewrite len_butlast. apply plus_n_O.
  - simpl. apply plus_n_Sm.
Qed.

