Require Import Nat Arith Bool.


Inductive Lst : Type := nil : Lst | cons : nat -> Lst -> Lst.

Fixpoint append (append_arg0 : Lst) (append_arg1 : Lst) : Lst
           := match append_arg0, append_arg1 with
              | nil, x => x
              | cons x y, z => cons x (append y z)
              end.

Fixpoint lst_mem (mem_arg0 : nat) (mem_arg1 : Lst) : bool
:= match mem_arg0, mem_arg1 with
    | x, nil => false
    | x, cons y z => orb (beq_nat x y) (lst_mem x z)
    end.

Fixpoint lst_subset (lst_subset_arg0 : Lst) (lst_subset_arg1 : Lst) : Prop
           := match lst_subset_arg0, lst_subset_arg1 with
              | nil, x => True
              | cons n x, y => and (lst_subset x y) (lst_mem n y = true)
              end.

Definition lst_eq (lst_eq_arg0 : Lst) (lst_eq_arg1 : Lst) : Prop
           := match lst_eq_arg0, lst_eq_arg1 with
              | x, y => and (lst_subset x y) (lst_subset y x)
              end.

Fixpoint lst_union (lst_union_arg0 : Lst) (lst_union_arg1 : Lst) : Lst
           := match lst_union_arg0, lst_union_arg1 with
              | nil, x => x
              | cons n x, y => if lst_mem n y then lst_union x y else cons n (lst_union x y)
              end.

      
Lemma subset_cons: forall l1 l2 n, lst_subset l1 l2 -> lst_subset l1 (cons n l2).
Proof.
  induction l1.
  - intros. reflexivity.
  - intros. simpl. split.
    * apply IHl1. inversion H. assumption.
    * destruct (beq_nat n n0). reflexivity. simpl.
      inversion H. assumption.
Qed.

Lemma beq_nat_refl: forall n, beq_nat n n = true.
Proof.
  induction n. reflexivity. simpl. assumption.
Qed.      

Lemma subset_refl : forall (x : Lst), lst_subset x x.
Proof.
induction x. simpl. reflexivity.
simpl. split. 
- apply subset_cons. assumption.
- rewrite beq_nat_refl. reflexivity.
Qed.


Theorem theorem0 : forall (x : Lst) (y : Lst), lst_subset x y -> lst_eq (lst_union x y) y.
Proof.
  intros.
  induction x.
  - simpl. unfold lst_eq. split.
    + apply subset_refl.
    + apply subset_refl.
  - simpl. simpl in H. destruct H. rewrite H0. apply IHx. assumption.
Qed.


(* This proof uses subset_cons above -- the goal is exactly the consequent of that lemma, but we also need a hypothesis. *)
Theorem theorem1: forall (x : Lst) (y : Lst), lst_subset x (append x y).
Proof.
  induction x.
  - intros. simpl. reflexivity.
  - intros. simpl. split.
    * apply subset_cons. apply IHx.
    * rewrite beq_nat_refl. simpl. reflexivity.
Qed.

(* This one does as well, and also reflexivity. Again, no synthesis or generalization. *)
Theorem theorem2: forall (x : Lst) (y : Lst), lst_subset y (append x y).
Proof.
  induction x.
  - intros. simpl. apply subset_refl.
  - intros. simpl. apply subset_cons. apply IHx.
Qed.

Lemma mem_union: forall n x y,
  lst_mem n y = true -> 
  lst_mem n (lst_union x y) = true.
intro. induction x.
- intros. simpl. assumption.
- intros. simpl. destruct (lst_mem n0 y).
  * apply IHx. assumption.
  * simpl. destruct (beq_nat n n0). reflexivity.
    simpl. apply IHx. assumption.
Qed.

(* Same here. *)
Theorem theorem3: forall (x : Lst) (y : Lst), lst_subset x (lst_union x y).
Proof.
  intros. induction x.
  - simpl. reflexivity.
  - simpl. split.
    * destruct (lst_mem n y).
      +  assumption.
      + apply subset_cons. assumption.
    * remember (lst_mem n y) as m.
      destruct m.
      -- apply mem_union. rewrite Heqm.
         reflexivity.
      -- simpl. rewrite beq_nat_refl. reflexivity.
Qed.