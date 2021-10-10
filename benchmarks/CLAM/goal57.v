Require Import Nat Arith.

Inductive Nat : Type := succ : Nat -> Nat |  zero : Nat.

Inductive Lst : Type := cons : Nat -> Lst -> Lst |  nil : Lst.

Inductive Tree : Type := node : Nat -> Tree -> Tree -> Tree |  leaf : Tree.

Inductive Pair : Type := mkpair : Nat -> Nat -> Pair
with ZLst : Type := zcons : Pair -> ZLst -> ZLst |  znil : ZLst.

Fixpoint drop (drop_arg0 : Nat) (drop_arg1 : Lst) : Lst
           := match drop_arg0, drop_arg1 with
              | x, nil => nil
              | zero, x => x
              | succ x, cons y z => drop x z
              end.

Theorem theorem0 : forall (u : Nat) (v : Nat) (w : Nat) (x : Nat) (y : Nat) (z : Lst),
  eq (drop (succ u) (drop v (drop (succ w) (cons x (cons y z))))) (drop (succ u) (drop v (drop w (cons x z)))).
Proof.
Admitted.

