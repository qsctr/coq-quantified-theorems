Require Import Nat Arith Bool.
Require Import Setoid.
Require Import Equivalence.

Inductive Lst : Type := nil : Lst | cons : nat -> Lst -> Lst.

Fixpoint append (append_arg0 : Lst) (append_arg1 : Lst) : Lst
           := match append_arg0, append_arg1 with
              | nil, x => x
              | cons x y, z => cons x (append y z)
              end.

Fixpoint rev (l : Lst) : Lst :=
  match l with
  | nil => nil
  | cons x y => append (rev y) (cons x nil)
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

Lemma beq_nat_refl: forall n, beq_nat n n = true.
Proof.
  induction n. reflexivity. simpl. assumption.
Qed.      

Lemma subset_cons: forall l1 l2 n, lst_subset l1 l2 -> lst_subset l1 (cons n l2).
Proof.
  induction l1.
  - intros. reflexivity.
  - intros. simpl. split.
    * apply IHl1. inversion H. assumption.
    * destruct (beq_nat n n0). reflexivity. simpl.
      inversion H. assumption.
Qed.


(* Transitivity is sufficient to enable the rewrite tactic to work, but reflexivity is also useful (e.g., for enabling the reflexivity tactic). *)

Instance subset_refl : Reflexive lst_subset.
Proof.
unfold Reflexive.
induction x. simpl. reflexivity.
simpl. split. 
- apply subset_cons. assumption.
- rewrite beq_nat_refl. reflexivity.
Qed.

Lemma subset_mem: forall x y n, lst_subset x y -> lst_mem n x = true -> lst_mem n y = true.
Proof.
  induction x.
  - intros. inversion H0.
  - intros. inversion H. inversion H0. unfold orb in H4. remember (n0 =? n) as b. destruct b.
    * assert ((n0 =? n) = true). rewrite Heqb. reflexivity. apply beq_nat_true in H3. rewrite H3. rewrite H2. simpl. reflexivity.
    * simpl. rewrite H4. apply (IHx y n0). assumption. assumption.
Qed.

Instance subset_trans: Transitive lst_subset.
Proof.
unfold Transitive.
induction x.
intros. reflexivity.
intros. simpl. inversion H. split.
- apply (IHx y z). assumption. assumption.
- apply (subset_mem y z n). assumption. assumption.
Qed.


Lemma subset_app: forall x n, lst_subset x (append x (cons n nil)).
Proof.
  induction x.
  - intros. reflexivity.
  - intros. simpl. split.
    * apply subset_cons. apply (IHx n0).
    * rewrite beq_nat_refl. reflexivity.
Qed.

Lemma mem_app: forall x n, lst_mem n (append x (cons n nil)) = true.
Proof.
  induction x.
  - intros. simpl. rewrite beq_nat_refl. reflexivity.
  - intros. simpl. destruct (n0 =? n).
    * simpl. reflexivity.
    * simpl. apply (IHx n0).
Qed.

Theorem subset_rev: forall x, lst_subset x (rev x).
Proof.
  induction x.
  - reflexivity.
  - simpl. split.
    * rewrite <- (subset_app (rev x) n). assumption.
    * apply (mem_app (rev x) n).
Qed.


Lemma subset_app2: forall x y z, lst_subset x z -> lst_subset y z -> lst_subset (append x y) z.
Proof.
  induction x.
  - intros. simpl. assumption.
  - intros. simpl. inversion H. split.
    * apply (IHx y z). assumption. assumption.
    * assumption.
Qed.
           
Add Morphism rev with signature (lst_subset ==> lst_subset) as rev_mor.
Proof.
  induction x.
  - intros. reflexivity.
  - intros. simpl. inversion H. apply IHx in H0. apply subset_app2.
    * assumption.
    * rewrite <- subset_rev. simpl. split. reflexivity. assumption.
Qed. 

Lemma mem_rev: forall n x, lst_mem n x = true -> lst_mem n (rev x) = true.
Proof.
  induction x.
  - intros. inversion H.
  - intros. simpl. inversion H. remember (n =? n0) as b. destruct b.
    * assert ((n =? n0) = true). rewrite Heqb. reflexivity. apply beq_nat_true in H0. rewrite H0. unfold orb. apply mem_app.
    * unfold orb. unfold orb in H1. rewrite H1.  apply IHx in H1.  apply (subset_mem (rev x) (append (rev x) (cons n0 nil)) n).
      + apply subset_app.
      + assumption.
Qed.

Theorem subset_rev_rev: forall x, lst_subset x (rev (rev x)).
Proof.
  induction x.
  - reflexivity.
  - simpl. split.
    * rewrite <- (subset_app (rev x) n). assumption.
    * apply mem_rev.  apply mem_app.
Qed.
