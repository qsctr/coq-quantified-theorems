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

Fixpoint fac (fac_arg0 : Nat) : Nat
           := match fac_arg0 with
              | zero => succ zero
              | succ n => mult (fac n) n
              end.

Fixpoint qfac (qfac_arg0 : Nat) (qfac_arg1 : Nat) : Nat
           := match qfac_arg0, qfac_arg1 with
              | zero, n => n
              | succ n, m => qfac n (mult m n)
              end.

Theorem theorem0 : forall (x : Nat) (y : Nat), eq (mult (fac x) y) (qfac x y).
Proof.
Admitted.

