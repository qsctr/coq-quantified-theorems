Require Import Nat Arith.

Inductive Lst : Type := cons : nat -> Lst -> Lst |  nil : Lst.

Fixpoint append (append_arg0 : Lst) (append_arg1 : Lst) : Lst
           := match append_arg0, append_arg1 with
              | nil, x => x
              | cons x y, z => cons x (append y z)
              end.

Fixpoint len (len_arg0 : Lst) : nat
           := match len_arg0 with
              | nil => 0
              | cons x y => plus 1 (len y)
              end.

Fixpoint butlast (butlast_arg0 : Lst) : Lst
           := match butlast_arg0 with
              | nil => nil
              | cons n x => if eqb x nil then nil else cons n (butlast x)
              end.

Theorem theorem0 : forall (x : Lst) (n : nat), eq (eqb (cons n x) nil) false.
Proof.
Admitted.

Theorem theorem1 : forall (x : Lst) (n : nat), eq (plus 1 (len (butlast (cons n x)))) (len (cons n x)).
Proof.
Admitted.

