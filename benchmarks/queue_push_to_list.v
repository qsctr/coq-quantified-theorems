Require Import Nat Arith.

Inductive Lst : Type := cons : nat -> Lst -> Lst |  nil : Lst.

Inductive Queue : Type := queue : Lst -> Lst -> Queue.

Fixpoint len (len_arg0 : Lst) : nat
           := match len_arg0 with
              | nil => 0
              | cons x y => plus 1 (len y)
              end.

Fixpoint qlen (qlen_arg0 : Queue) : nat
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

Fixpoint amortizeQueue (amortizeQueue_arg0 : Lst) (amortizeQueue_arg1 : Lst) : Queue
           := match amortizeQueue_arg0, amortizeQueue_arg1 with
              | x, y => if leb (len y) (len x) then queue x y else queue (append x (rev y)) nil
              end.

Fixpoint qpush (qpush_arg0 : Queue) (qpush_arg1 : nat) : Queue
           := match qpush_arg0, qpush_arg1 with
              | queue x y, n => amortizeQueue x (cons n y)
              end.

Fixpoint queue_to_lst (queue_to_lst_arg0 : Queue) : Lst
           := let 'queue x y := queue_to_lst_arg0 in
              append x (rev y).

Theorem theorem0 : forall (q : Queue) (n : nat), eq (append (queue_to_lst q) (cons n nil)) (queue_to_lst (qpush q n)).
Proof.
Admitted.

