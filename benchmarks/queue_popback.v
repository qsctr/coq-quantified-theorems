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

Fixpoint butlast (butlast_arg0 : Lst) : Lst
           := match butlast_arg0 with
              | nil => nil
              | cons n x => if eqb x nil then nil else cons n (butlast x)
              end.

Fixpoint qpopback (qpopback_arg0 : Queue) : Queue
           := match qpopback_arg0 with
              | queue x (cons n y) => queue x y
              | queue x nil => queue (butlast x) nil
              end.

Fixpoint isAmortized (isAmortized_arg0 : Queue) : bool
           := let 'queue x y := isAmortized_arg0 in
              leb (len y) (len x).

Fixpoint isEmpty (isEmpty_arg0 : Queue) : bool
           := let 'queue x y := isEmpty_arg0 in
              andb (eqb x nil) (eqb y nil).

Theorem theorem0 : forall (q : Queue) (n : nat), and (eq (isAmortized q) true) (not (eq (isEmpty q) true)) -> eq (plus 1 (qlen (qpopback q))) (qlen q).
Proof.
Admitted.

