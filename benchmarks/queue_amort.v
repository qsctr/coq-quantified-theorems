Require Import Nat Arith.

Inductive Lst : Type := cons : nat -> Lst -> Lst |  nil : Lst.

Inductive Queue : Type := queue : Lst -> Lst -> Queue.

Fixpoint len (len_arg0 : Lst) : nat
           := match len_arg0 with
              | nil => 0
              | cons x y => plus 1 (len y)
              end.

Fixpoint append (append_arg0 : Lst) (append_arg1 : Lst) : Lst
           := match append_arg0, append_arg1 with
              | nil, x => x
              | cons x y, z => cons x (append y z)
              end.

Fixpoint rev2 (rev2_arg0 : Lst) (rev2_arg1 : Lst) : Lst
           := match rev2_arg0, rev2_arg1 with
              | nil, a => a
              | cons x t, a => rev2 t (cons x a)
              end.

Fixpoint qrev (qrev_arg0 : Lst) : Lst
           := let 'x := qrev_arg0 in
              rev2 x nil.

Fixpoint amortizeQueue (amortizeQueue_arg0 : Lst) (amortizeQueue_arg1 : Lst) : Queue
           := match amortizeQueue_arg0, amortizeQueue_arg1 with
              | x, y => if leb (len y) (len x) then queue x y else queue (append x (qrev y)) nil
              end.

Fixpoint isAmortized (isAmortized_arg0 : Queue) : bool
           := let 'queue x y := isAmortized_arg0 in
              leb (len y) (len x).

Theorem theorem0 : forall (x : Lst) (y : Lst), eq (isAmortized (amortizeQueue x y)) true.
Proof.
Admitted.

