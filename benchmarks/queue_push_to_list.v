Require Import Nat Arith.

Inductive Lst : Type := nil : Lst | cons : nat -> Lst -> Lst.

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

Fixpoint rev (rev_arg0 : Lst) : Lst
           := match rev_arg0 with
              | nil => nil
              | cons x y => append (rev y) (cons x nil)
              end.

Definition amortizeQueue (amortizeQueue_arg0 : Lst) (amortizeQueue_arg1 : Lst) : Queue
           := match amortizeQueue_arg0, amortizeQueue_arg1 with
              | x, y => if leb (len y) (len x) then queue x y else queue (append x (rev y)) nil
              end.

Definition qpush (qpush_arg0 : Queue) (qpush_arg1 : nat) : Queue
           := match qpush_arg0, qpush_arg1 with
              | queue x y, n => amortizeQueue x (cons n y)
              end.

Definition queue_to_lst (queue_to_lst_arg0 : Queue) : Lst
           := let 'queue x y := queue_to_lst_arg0 in
              append x (rev y).

Lemma append_nil : forall (l : Lst), append l nil = l.
Proof.
  intros.
  induction l.
  - reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Theorem theorem0 : forall (q : Queue) (n : nat), eq (append (queue_to_lst q) (cons n nil)) (queue_to_lst (qpush q n)).
Proof.
  intros.
  destruct q.
  induction l.
  - simpl. rewrite append_nil. reflexivity.
  - simpl. simpl in IHl. rewrite IHl. unfold amortizeQueue. simpl. destruct (len l) eqn:?.
    + simpl. destruct (len l0 <=? 0) eqn:?.
      * simpl. rewrite append_nil. reflexivity.
      * simpl. reflexivity.
    + destruct (len l0 <=? n1) eqn:?.
      * simpl. apply Nat.leb_le in Heqb. apply le_S in Heqb. rewrite <- Nat.leb_le in Heqb. rewrite Heqb. simpl. reflexivity.
      * destruct (len l0 <=? S n1) eqn:?.
        -- simpl. rewrite append_nil. reflexivity.
        -- simpl. reflexivity.
Qed.

