Require Import Nat Arith.

Inductive Nat : Type := succ : Nat -> Nat |  zero : Nat.

Inductive Lst : Type := cons : Nat -> Lst -> Lst |  nil : Lst.

Inductive Tree : Type := node : Nat -> Tree -> Tree -> Tree |  leaf : Tree.

Inductive Pair : Type := mkpair : Nat -> Nat -> Pair
with ZLst : Type := zcons : Pair -> ZLst -> ZLst |  znil : ZLst.

Fixpoint plus (plus_arg0 : Nat) (plus_arg1 : Nat) : Nat
           := match plus_arg0, plus_arg1 with
              | zero, n => n
              | succ n, m => succ (plus n m)
              end.

Fixpoint mult (mult_arg0 : Nat) (mult_arg1 : Nat) : Nat
           := match mult_arg0, mult_arg1 with
              | zero, n => zero
              | succ n, m => plus (mult n m) m
              end.

Fixpoint qmult (qmult_arg0 : Nat) (qmult_arg1 : Nat) (qmult_arg2 : Nat) : Nat
           := match qmult_arg0, qmult_arg1, qmult_arg2 with
              | zero, n, m => m
              | succ n, m, p => qmult n m (plus p m)
              end.

Theorem theorem0 : forall (x : Nat) (y : Nat), eq (mult x y) (qmult x y zero).
Proof.
Admitted.

