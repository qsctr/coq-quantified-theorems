Require Import Nat Arith.

Inductive Lst : Type := cons : nat -> Lst -> Lst |  nil : Lst.

Fixpoint double (double_arg0 : nat) : nat
           := match double_arg0 with
              | O => O
              | S n' => S (S (double n'))
              end.

Lemma lem: forall m n, S (plus m n) = plus m (S n).
Proof.
   induction m.
   - intros. simpl. reflexivity.
   - intros. simpl. rewrite IHm. reflexivity.
Qed.

(* These theorems require a helper lemma (see above) that is an equality. *)

Theorem theorem0 : forall (x : nat), (double x) < (S (plus x x)).
Proof.
   induction x.
   - simpl. apply lt_O_Sn.
   - simpl. apply lt_n_S. apply lt_n_S. rewrite <- lem. assumption.
Qed.

Theorem theorem1 : forall (x : nat), (plus x x) < (S (double x)).
Proof.
   induction x.
   - simpl. apply lt_O_Sn.
   - simpl. apply lt_n_S. rewrite <- lem. apply lt_n_S. assumption.
Qed.

