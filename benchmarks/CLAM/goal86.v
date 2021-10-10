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

Fixpoint exp (exp_arg0 : Nat) (exp_arg1 : Nat) : Nat
           := match exp_arg0, exp_arg1 with
              | n, zero => succ zero
              | n, succ m => mult (exp n m) n
              end.

Fixpoint qexp (qexp_arg0 : Nat) (qexp_arg1 : Nat) (qexp_arg2 : Nat) : Nat
           := match qexp_arg0, qexp_arg1, qexp_arg2 with
              | n, zero, m => m
              | n, succ m, p => qexp n m (mult p n)
              end.

Theorem theorem0 : forall (x : Nat) (y : Nat) (z : Nat), eq (mult (exp x y) z) (qexp x y z).
Proof.
Admitted.

