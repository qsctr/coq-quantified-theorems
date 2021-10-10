Require Import Nat Arith.

Inductive Tree : Type := node : nat -> Tree -> Tree -> Tree |  leaf : Tree.

Fixpoint tinsert (tinsert_arg0 : Tree) (tinsert_arg1 : nat) : Tree
           := match tinsert_arg0, tinsert_arg1 with
              | leaf, i => node i leaf leaf
              | node d l r, i => if ltb d i then node d l (tinsert r i) else node d (tinsert l i) r
              end.

Fixpoint tsize (tsize_arg0 : Tree) : nat
           := match tsize_arg0 with
              | leaf => 0
              | node x l r => plus 1 (plus (tsize l) (tsize r))
              end.

Theorem theorem0 : forall (t : Tree) (n : nat), eq (tsize (tinsert t n)) (plus 1 (tsize t)).
Proof.
Admitted.

