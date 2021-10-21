Require Import Nat Arith.

Inductive Nat : Type := succ : Nat -> Nat |  zero : Nat.

Inductive Lst : Type := cons : Nat -> Lst -> Lst |  nil : Lst.

Inductive Tree : Type := node : Nat -> Tree -> Tree -> Tree |  leaf : Tree.

Inductive Pair : Type := mkpair : Nat -> Nat -> Pair
with ZLst : Type := zcons : Pair -> ZLst -> ZLst |  znil : ZLst.

Fixpoint append (append_arg0 : Lst) (append_arg1 : Lst) : Lst
           := match append_arg0, append_arg1 with
              | nil, x => x
              | cons x y, z => cons x (append y z)
              end.

Fixpoint rev (rev_arg0 : Lst) : Lst
           := match rev_arg0 with
              | nil => nil
              | cons x y => append (rev y) (cons x nil)
              end.

Lemma lem : forall (x : Lst) (y : Nat), eq (rev (append x (cons y nil))) (cons y (rev x)).
Proof.
induction x.
- intros. simpl. rewrite IHx. reflexivity.
- intros. reflexivity.
Qed.

Theorem theorem0 : forall (x : Lst) (y : Lst) (z : Nat), eq (rev (append x (append y (cons z nil)))) (cons z (rev (append x y))).
Proof.
induction x.
- intros. simpl. rewrite IHx. reflexivity.
- intros. simpl. apply lem.
Qed.


