Require Import Nat Arith.

Inductive Lst : Type := cons : nat -> Lst -> Lst |  nil : Lst.

Inductive Heap : Type := hleaf : Heap |  heap : nat -> nat -> Heap -> Heap -> Heap.

Fixpoint rightHeight (rightHeight_arg0 : Heap) : nat
           := match rightHeight_arg0 with
              | hleaf => 0
              | heap k v l r => plus 1 (rightHeight r)
              end.

Fixpoint rank (rank_arg0 : Heap) : nat
           := match rank_arg0 with
              | hleaf => 0
              | heap k v l r => k
              end.

Fixpoint hasLeftistProperty (hasLeftistProperty_arg0 : Heap) : bool
           := match hasLeftistProperty_arg0 with
              | hleaf => true
              | heap k v l r =>
                  andb (hasLeftistProperty l) (andb (hasLeftistProperty r) (andb (leb (rightHeight r) (rightHeight l)) (eqb k (plus 1 (rightHeight r)))))
              end.

Fixpoint hsize (hsize_arg0 : Heap) : nat
           := match hsize_arg0 with
              | hleaf => 0
              | heap k v l r => plus 1 (plus (hsize l) (hsize r))
              end.

Fixpoint mergea (mergea_arg0 : nat) (mergea_arg1 : Heap) (mergea_arg2 : Heap) : Heap
           := match mergea_arg0, mergea_arg1, mergea_arg2 with
              | v, l, r => if leb (rank r) (rank l) then heap (plus 1 (rank r)) v l r else heap (plus 1 (rank l)) v r l
              end.

Fixpoint merge (merge_arg0 : Heap) (merge_arg1 : Heap) : Heap
           := match merge_arg0, merge_arg1 with
              | h, hleaf => h
              | hleaf, h => h
              | heap k1 v1 l1 r1, heap k2 v2 l2 r2 =>
                  if ltb v2 v1
                  then mergea v1 l1 (merge r1 (heap k2 v2 l2 r2))
                  else mergea v2 l2 (merge (heap k1 v1 l1 r1) r2)
              end.

Fixpoint hinsert (hinsert_arg0 : Heap) (hinsert_arg1 : nat) : Heap
           := match hinsert_arg0, hinsert_arg1 with
              | h, n => merge (heap 1 n hleaf hleaf) h
              end.

Fixpoint hinsert_all (hinsert_all_arg0 : Lst) (hinsert_all_arg1 : Heap) : Heap
           := match hinsert_all_arg0, hinsert_all_arg1 with
              | nil, h => h
              | cons n l, h => hinsert (hinsert_all l h) n
              end.

Theorem theorem0 : forall (x : Heap) (n : nat), eq (hasLeftistProperty x) true -> eq (hasLeftistProperty (hinsert x n)) true.
Proof.
Admitted.

Theorem theorem1 : forall (l : Lst) (h : Heap), eq (hasLeftistProperty h) true -> eq (hasLeftistProperty (hinsert_all l h)) true.
Proof.
Admitted.

