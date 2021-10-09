Require Import Bool.
Require Import Arith.

Inductive lst : Type :=
| Cons : nat -> lst -> lst
| Nil : lst.

Inductive heap : Type :=
| Hleaf : heap
| Heap : nat -> nat -> heap -> heap -> heap.

Fixpoint right_height (h : heap) : nat :=
  match h with
  | Hleaf => 0
  | Heap k v l r => right_height r + 1
  end.

Definition rank (h : heap) : nat :=
  match h with
  | Hleaf => 0
  | Heap k v l r => k
  end.

Fixpoint has_leftist_property (h : heap) : Prop :=
  match h with
  | Hleaf => True
  | Heap k v l r =>
    has_leftist_property l
    /\ has_leftist_property r
    /\ (right_height r <= right_height l)
    /\ (k = right_height r + 1)
  end.

Fixpoint hsize (h : heap) : nat :=
  match h with
  | Hleaf => 0
  | Heap k v l r => hsize l + hsize r + 1
  end.

Definition mergea (v : nat) (l r : heap) : heap :=
  if rank r <=? rank l
    then Heap (rank r + 1) v l r
    else Heap (rank l + 1) v r l.

Fixpoint merge (h1 : heap) : heap -> heap :=
  fix merge_aux (h2 : heap) : heap :=
  match h1, h2 with
  | h, Hleaf => h
  | Hleaf, h => h
  | Heap k1 v1 l1 r1, Heap k2 v2 l2 r2 =>
    if v2 <? v1
      then mergea v1 l1 (merge r1 (Heap k2 v2 l2 r2))
      else mergea v2 l2 (merge_aux r2)
  end.

Definition hinsert (h : heap) (n : nat) : heap :=
  merge (Heap 1 n Hleaf Hleaf) h.

(* Require Coq.extraction.Extraction.

Recursive Extraction hinsert. *)

Lemma hsize_nonneg : forall h : heap, hsize h >= 0.
Proof.
  (* This lemma is trivial since we use nat instead of Int. *)
  intros.
  induction (hsize h).
  - auto.
  - auto.
Qed.

Lemma rank_right_height : forall h : heap,
  has_leftist_property h -> rank h = right_height h.
Proof.
  intros.
  induction h.
  - auto.
  - inversion H. tauto.
Qed.

Lemma leftist_mergea : forall (v : nat) (l r : heap),
  has_leftist_property l /\ has_leftist_property r
    -> has_leftist_property (mergea v l r).
Proof.
  intros.
  unfold mergea.
  destruct H.
  destruct (Nat.leb_spec (rank r) (rank l)).
  - rewrite (rank_right_height r H0) in H1.
    rewrite (rank_right_height l H) in H1.
    simpl. rewrite (rank_right_height r H0). auto.
  - rewrite (rank_right_height r H0) in H1.
    rewrite (rank_right_height l H) in H1.
    simpl. rewrite (rank_right_height l H).
    apply le_Sn_le in H1. auto.
Qed.

Lemma leftist_merge : forall h1 h2 : heap,
  has_leftist_property h1 /\ has_leftist_property h2
    -> has_leftist_property (merge h1 h2).
Proof.
  intro h1.
  induction h1.
  - intros. destruct h2.
    + reflexivity.
    + simpl. simpl in H. tauto.
  - intros. induction h2.
    + simpl. simpl in H. tauto.
    + destruct H. simpl in H. simpl. destruct (n2 <? n0).
      * apply leftist_mergea. split.
        -- tauto.
        -- apply IHh1_2. tauto.
      * simpl in H0. simpl in IHh2_2. apply leftist_mergea. split.
        -- tauto.
        -- apply IHh2_2. tauto.
Qed.

Theorem leftist_hinsert : forall (x : heap) (n : nat),
  has_leftist_property x -> has_leftist_property (hinsert x n).
Proof.
  intros. unfold hinsert. apply leftist_merge. split.
  - unfold has_leftist_property. auto.
  - assumption.
Qed.
