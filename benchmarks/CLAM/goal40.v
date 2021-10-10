Require Import Nat Arith.

Inductive Nat : Type := succ : Nat -> Nat |  zero : Nat.

Inductive Lst : Type := cons : Nat -> Lst -> Lst |  nil : Lst.

Inductive Tree : Type := node : Nat -> Tree -> Tree -> Tree |  leaf : Tree.

Inductive Pair : Type := mkpair : Nat -> Nat -> Pair
with ZLst : Type := zcons : Pair -> ZLst -> ZLst |  znil : ZLst.

Fixpoint lst_mem (lst_mem_arg0 : Nat) (lst_mem_arg1 : Lst) : bool
           := match lst_mem_arg0, lst_mem_arg1 with
              | n, x => mem n x
              end.

Fixpoint lst_subset (lst_subset_arg0 : Lst) (lst_subset_arg1 : Lst) : bool
           := match lst_subset_arg0, lst_subset_arg1 with
              | nil, x => true
              | cons n x, y => andb (lst_subset x y) (lst_mem n y)
              end.

Fixpoint lst_eq (lst_eq_arg0 : Lst) (lst_eq_arg1 : Lst) : bool
           := match lst_eq_arg0, lst_eq_arg1 with
              | x, y => andb (lst_subset x y) (lst_subset y x)
              end.

Fixpoint lst_union (lst_union_arg0 : Lst) (lst_union_arg1 : Lst) : Lst
           := match lst_union_arg0, lst_union_arg1 with
              | nil, x => x
              | cons n x, y => if lst_mem n y then lst_union x y else cons n (lst_union x y)
              end.

Theorem theorem0 : forall (x : Lst) (y : Lst), eq (lst_subset x y) true -> eq (lst_eq (lst_union x y) y) true.
Proof.
Admitted.

