(* From coq-projects/circuits/ *)
Require Import Bool.
Require Import Arith.

(* GENE/Arith_compl.v *)
Require Export Plus.
Require Export Mult.
Require Import Minus.
Require Export Lt.
Require Export Le.
Require Export Gt.

(****************************************************************)
(* Complements sur plus et mult *)

Lemma plus_n_SO : forall x : nat, x + 1 = S x.
intros; rewrite plus_comm; auto with arith.
Qed.

Lemma plus_permute2 : forall x y z : nat, x + y + z = x + z + y.
intros.
rewrite (plus_comm x y).
rewrite (plus_comm x z).
rewrite plus_comm.
symmetry  in |- *.
rewrite plus_comm.
rewrite plus_permute.
auto with arith.
Qed.

Lemma mult_sym : forall a b : nat, a * b = b * a.
intros a b; elim a; simpl in |- *; auto with arith.
intros y H.
replace (y * b) with (b * y).
elim (mult_n_Sm b y).
apply plus_comm.
Qed.

Lemma mult_permute : forall a b c : nat, a * b * c = a * c * b.
intros.
rewrite mult_assoc_reverse.
rewrite mult_assoc_reverse.
replace (c * b) with (b * c); auto with arith.
Qed.


Lemma plus_O_O : forall n m : nat, n + m = 0 -> n = 0.
simple induction n. intros. trivial with arith.
intros. inversion H0.
Qed.

Lemma mult_plus_distr2 : forall n m p : nat, n * (m + p) = n * m + n * p.
intros. rewrite mult_sym. rewrite mult_plus_distr_r. rewrite mult_sym.
replace (p * n) with (n * p). trivial with arith. apply mult_sym.
Qed.

(****************************************************************)
(* La fonction puissance de 2 *)

Fixpoint power2 (n : nat) : nat :=
  match n with
  | O => 1
  | S x => power2 x + power2 x
  end.

Lemma power2_eq2 : forall x : nat, power2 (S x) = power2 x + power2 x.
Proof.
 auto with arith.
Qed.


Lemma power2_plus : forall x y : nat, power2 (x + y) = power2 x * power2 y.
simple induction x. intros. simpl in |- *. elim plus_n_O; auto with arith.
intros. simpl in |- *. rewrite H. rewrite mult_plus_distr_r. trivial with arith.
Qed.

(****************************************************************)
(* Complements sur Lt Le Gt... *)

Theorem le_plus_n_m : forall n m : nat, n <= m -> n + n <= m + m.
simple induction n. auto with arith.
intros. inversion H0. auto with arith.
simpl in |- *. elim plus_n_Sm. elim plus_n_Sm.
apply le_n_S. apply le_n_S. apply H. apply le_Sn_le. exact H1.
Qed.

Theorem lt_plus_n_m : forall n m : nat, n < m -> S (n + n) < m + m.
simple induction n.
simpl in |- *. simple induction m. simpl in |- *. intros. absurd (0 < 0). apply le_not_lt. auto with arith.
exact H.
intros. simpl in |- *. elim plus_n_Sm. apply lt_n_S. auto with arith.
intros. inversion H0. simpl in |- *. repeat elim plus_n_Sm. auto with arith.
simpl in |- *.
repeat elim plus_n_Sm. apply lt_n_S. apply lt_n_S. apply H. inversion H1. auto with arith.
apply le_lt_n_Sm. apply le_Sn_le. apply le_Sn_le. exact H3.
Qed.

Lemma le_plus_lem1 : forall a b c : nat, a <= b -> c + a <= c + b.
intros. inversion H. auto with arith.
elim plus_n_Sm. apply le_S. auto with arith.
Qed.

Lemma le_plus_lem2 : forall a b c : nat, c + a <= c + b -> a <= b.
simple induction c. auto with arith.
simpl in |- *. intros. apply H. apply le_S_n. exact H0.
Qed.

Lemma gt_double : forall a b : nat, a + a > b + b -> a > b.
simple induction a. simpl in |- *. intros. absurd (0 > b + b). auto with arith.
auto with arith. simple induction b. simpl in |- *. auto with arith.
intros. apply gt_n_S.
apply H. generalize H1. simpl in |- *. elim plus_n_Sm. elim plus_n_Sm. intro.
cut (S (n + n) > S (n0 + n0)). intro. apply gt_S_n. exact H3.
apply gt_S_n. exact H2.
Qed.

Lemma gt_double_inv : forall a b : nat, a > b -> a + a > b + b.
simple induction a. intros. absurd (0 > b). auto with arith. exact H.
simple induction b. intros. simpl in |- *. auto with arith.
intros. simpl in |- *. elim plus_n_Sm.
elim plus_n_Sm. apply gt_n_S. apply gt_n_S. apply H. apply gt_S_n. exact H1.
Qed.

Lemma gt_double_n_S : forall a b : nat, a > b -> a + a > S (b + b).
simple induction a. intros. absurd (0 > b). auto with arith.
exact H.
simple induction b. simpl in |- *. intro.
apply gt_n_S. unfold gt in |- *. unfold lt in |- *. elim plus_n_Sm. auto with arith.
intros. simpl in |- *. apply gt_n_S.
elim plus_n_Sm. apply gt_n_S. elim plus_n_Sm. apply H. apply gt_S_n. exact H1.
Qed.

Lemma gt_double_S_n : forall a b : nat, a > b -> S (a + a) > b + b.
intros. apply gt_trans with (a + a). auto with arith. apply gt_double_inv. exact H.
Qed.

(****************************************************************)
(* Complements sur minus *)

Lemma minus_le_O : forall a b : nat, a <= b -> a - b = 0.
intros. pattern a, b in |- *. apply le_elim_rel. auto with arith.
intros. simpl in |- *. exact H1.
exact H.
Qed.

Lemma minus_n_SO : forall n : nat, n - 1 = pred n.
simple induction n. auto with arith. intros. simpl in |- *. auto with arith.
Qed.

Lemma minus_le_lem2c : forall a b : nat, a - S b <= a - b.
intros. pattern a, b in |- *. apply nat_double_ind. auto with arith.
intro. elim minus_n_O. rewrite minus_n_SO. simpl in |- *. auto with arith.
intros. simpl in |- *. exact H.
Qed.

Lemma minus_le_lem2 : forall a b : nat, a - b <= a.
simple induction b. elim minus_n_O. auto with arith.
intros. apply le_trans with (a - n). apply minus_le_lem2c.
exact H.
Qed.

Lemma minus_minus_lem1 : forall a b : nat, a - b - a = 0.
intros. apply minus_le_O. apply minus_le_lem2.
Qed.

Lemma minus_minus_lem2 : forall a b : nat, b <= a -> a - (a - b) = b.
simple induction b. intros. elim minus_n_O. elim minus_n_n. trivial with arith. intros.
replace (a - (a - S n)) with (S a - S (a - S n)).
rewrite <- (minus_Sn_m a (S (a - S n))). rewrite (minus_Sn_m a (S n)).
simpl in |- *. rewrite <- H. rewrite H. rewrite H. trivial with arith.
apply le_Sn_le. exact H0.
apply le_Sn_le. exact H0. apply le_Sn_le. exact H0. exact H0.
rewrite minus_Sn_m. simpl in |- *. apply minus_le_lem2. exact H0. simpl in |- *. trivial with arith.
Qed.

Lemma le_minus_minus : forall a b c : nat, c <= b -> a - b <= a - c.
simple induction a. simpl in |- *. auto with arith.
intros. generalize H0. elim c. elim minus_n_O. intro. apply minus_le_lem2.
elim b. intros. absurd (S n0 <= 0). auto with arith.
exact H2.
intros. simpl in |- *. apply H. apply le_S_n. exact H3.
Qed.

(* Bool_compl.v *)
Definition bool_to_nat (b : bool) :=
  match b with
  | true => 1
  | false => 0
  end.

Lemma neg_eq : forall a b : bool, negb a = negb b -> a = b.
simple induction a; simple induction b; auto.
Qed.

Lemma false_to_true : false = negb true.
auto.
Qed.

Lemma true_to_false : true = negb false.
auto.
Qed.

Definition xorb (b1 b2 : bool) : bool := b1 && negb b2 || negb b1 && b2.

Lemma xorb_b_b : forall b : bool, xorb b b = false.
simple induction b; auto.
Qed.

Lemma xorb_b_false : forall b : bool, xorb b false = b.
simple induction b; auto.
Qed.

Lemma xorb_b_true : forall b : bool, xorb b true = negb b.
simple induction b; auto.
Qed.


Lemma bool_to_nat_all :
 forall b : bool, bool_to_nat b = 0 \/ bool_to_nat b = 1.
simple induction b; auto.
Qed.



(* ADDER/HalfAdder.v *)
Definition half_adder_sum (a b : bool) := xorb a b.
Definition half_adder_carry (a b : bool) := a && b.


Lemma half_adder_sum_sym:
  forall a b: bool, half_adder_sum a b = half_adder_sum b a.
  induction a; induction b; auto.
Qed.

Lemma half_adder_carry_sym:
  forall a b: bool, half_adder_carry a b = half_adder_carry b a.
simple  induction a; induction b; auto.
Qed.

Lemma half_adder_sum_false : forall a : bool, half_adder_sum a false = a.
simple induction a; auto.
Qed.

Lemma half_adder_carry_false :
 forall a : bool, half_adder_carry a false = false.
simple induction a; auto.
Qed.

Lemma half_adder_sum_true : forall a : bool, half_adder_sum a true = negb a.
  intros.
  induction a.
  simpl.
  unfold half_adder_sum. auto.
  unfold half_adder_sum. auto.
Qed.

Lemma half_adder_carry_true : forall a : bool, half_adder_carry a true = a.
simple induction a; auto.
Qed.

Theorem half_adder_ok :
 forall a b : bool,
 bool_to_nat (half_adder_sum a b) +
 (bool_to_nat (half_adder_carry a b) + bool_to_nat (half_adder_carry a b)) =
 bool_to_nat a + bool_to_nat b.
simple induction a; simple induction b; auto.
Qed.


(* ADDER/FullAdder.v *)
Definition full_adder_sum (a b c : bool) :=
  half_adder_sum (half_adder_sum a b) c.

Definition full_adder_carry (a b c : bool) :=
  half_adder_carry a b || half_adder_carry (half_adder_sum a b) c.

Lemma full_adder_sum_sym1 :
 forall a b c : bool, full_adder_sum a b c = full_adder_sum b a c.
simple induction a; simple induction b; auto.
Qed.

Lemma full_adder_sum_sym2 :
 forall a b c : bool, full_adder_sum a b c = full_adder_sum a c b.
simple induction b.
simple induction c.
auto.
unfold full_adder_sum in |- *.
rewrite half_adder_sum_false.
rewrite half_adder_sum_false.
auto.
unfold full_adder_sum in |- *.
rewrite half_adder_sum_false.
intro.
rewrite half_adder_sum_false.
auto.
Qed.

Lemma full_adder_sum_false :
 forall a : bool, full_adder_sum a false false = a.
simple induction a; auto.
Qed.

Lemma full_adder_sum_true : forall a : bool, full_adder_sum a true true = a.
simple induction a; auto.
Qed.

Lemma full_adder_carry_sym1 :
 forall a b c : bool, full_adder_carry a b c = full_adder_carry b a c.
simple induction a; simple induction b; auto.
Qed.

Lemma full_adder_carry_sym2 :
 forall a b c : bool, full_adder_carry a b c = full_adder_carry a c b.
simple induction b.
simple induction c.
auto.
unfold full_adder_carry in |- *.
rewrite half_adder_sum_false.
rewrite half_adder_carry_false.
rewrite half_adder_carry_false.
simpl in |- *.
elim (half_adder_carry a true); auto.
intros.
unfold full_adder_carry in |- *.
rewrite half_adder_carry_false.
rewrite half_adder_sum_false.
rewrite half_adder_carry_false.
simpl in |- *.
elim (half_adder_carry a c); auto.
Qed.

Lemma full_adder_carry_false :
 forall a : bool, full_adder_carry a false false = false.
simple induction a; auto.
Qed.

Lemma full_adder_carry_true :
 forall a : bool, full_adder_carry a true true = true.
simple induction a.
unfold full_adder_carry in |- *.
auto.
unfold full_adder_carry in |- *.
auto.
Qed.

Lemma full_adder_carry_true_false :
 forall a : bool, full_adder_carry a true false = a.
simple induction a; auto.
Qed.

Lemma full_adder_carry_neg :
 forall a b : bool, full_adder_carry a (negb a) b = b.
simple induction a; simple induction b; simpl in |- *.
rewrite full_adder_carry_sym1. rewrite full_adder_carry_true. trivial.
rewrite full_adder_carry_false. trivial.
rewrite full_adder_carry_true. trivial.
rewrite full_adder_carry_sym1. rewrite full_adder_carry_false. trivial.
Qed.

(****************************************************************)

Theorem full_adder_ok :
 forall a b c : bool,
 bool_to_nat (full_adder_sum a b c) +
 (bool_to_nat (full_adder_carry a b c) + bool_to_nat (full_adder_carry a b c)) =
 bool_to_nat a + bool_to_nat b + bool_to_nat c.
simple induction a; simple induction b; simple induction c; auto.
Qed.

(* BoolList *)
Inductive BoolList : Type :=
| nil : BoolList
| cons : bool -> BoolList -> BoolList.

Infix "::" := cons (at level 60, right associativity).

Definition length : BoolList -> nat :=
  fix length l :=
  match l with
   | nil => O
   | _ :: l' => S (length l')
  end.

Definition app : BoolList -> BoolList -> BoolList :=
  fix app l m :=
  match l with
   | nil => m
   | a :: l1 => a :: app l1 m
  end.

Infix "++" := app (right associativity, at level 60).

Definition tail (l:BoolList) : BoolList :=
  match l with
  | nil => nil
  | a :: m => m
  end.

(* Lists_compl.v *)
Lemma length_eq1 : length (nil:BoolList) = 0.
auto with arith. Qed.
Lemma length_eq2 :
 forall (x : bool) (l : BoolList), length (x :: l) = S (length l).
auto with arith. Qed.

Lemma app_eq1 : forall l' : BoolList, nil ++ l' = l'.
auto with arith. Qed.
Lemma app_eq2 : forall (x : bool) (l l' : BoolList), (x :: l) ++ l' = x :: l ++ l'.
auto with arith. Qed.

Lemma nil_cons : forall (b : bool) (v : BoolList), nil <> b :: v.
(*************)
intros. discriminate.
Qed.

Lemma not_cons_eq : forall (v : BoolList) (b : bool), v <> b :: v.
(****************)
simple induction v. intro. discriminate.
intros. injection. intros. absurd (b0 = b :: b0). apply H.
exact H1.
Qed.

Lemma app_nil_end : forall l:BoolList, l = l ++ nil.
Proof.
        induction l; simpl in |- *; auto.
        rewrite <- IHl; auto.
Qed.

Lemma app_v_nil : forall v : BoolList, v ++ nil = v.
(**************)
intro.
rewrite <- app_nil_end; trivial with arith.
Qed.

Lemma app_v_nil_idem : forall v v' : BoolList, v = v' -> v ++ nil = v'.
(********************)
intros. inversion H. apply app_v_nil.
Qed.

Lemma app_v_nil_inv : forall v1 v2 : BoolList, v1 ++ v2 = v1 -> v2 = nil.
(******************)
simple induction v1. simpl in |- *. trivial with arith.
intros. generalize H0. rewrite app_eq2. intros. injection H1. intro. apply H. exact H2.
Qed.

Lemma app_v_nil_sym : forall v1 v2 : BoolList, v1 = nil -> v1 ++ v2 = v2 ++ v1.
(******************)
simple induction v2. intro. rewrite H. trivial with arith.
intros. rewrite H0. simpl. apply app_nil_end.
Qed.

Lemma app_assoc_r : forall l m n:BoolList, (l ++ m) ++ n = l ++ m ++ n.
Proof.
        intros. induction l; simpl in |- *; auto.
        now_show (b :: (l ++ m) ++ n = b :: l ++ m ++ n).
        rewrite <- IHl; auto.
Qed.
Lemma app_assoc_l : forall l m n:BoolList, l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros. rewrite app_assoc_r. reflexivity.
Qed.


Lemma length_eq : forall v1 v2 : BoolList, v1 = v2 -> length v1 = length v2.
(**************)
intros. rewrite H. trivial with arith.
Qed.

Lemma not_nil : forall v : BoolList, length v <> 0 -> v <> nil.
(************)
simple induction v. simpl in |- *; intro. absurd (0 <> 0). unfold not in |- *; auto with arith. exact H.
simpl in |- *. intros. discriminate.
Qed.

Lemma length_app :
 forall v1 v2 : BoolList,
 (***************)
 length (v1 ++ v2) = length v1 + length v2.
simple induction v1. simpl in |- *. trivial with arith.
intros. simpl in |- *. rewrite H. trivial with arith.
Qed.

Lemma v_not_nil_length :
 forall v : BoolList,
 (*********************)
 v <> nil -> 1 <= length v.
simple induction v. intro. absurd (nil <> nil :>BoolList). unfold not in |- *. auto with arith.
exact H.
intros. simpl in |- *. apply le_n_S. auto with arith.
Qed.

Lemma le_SO_length_v :
 forall v : BoolList,
 (*******************)
 length v <> 0 -> 1 <= length v.
intros. apply v_not_nil_length. apply not_nil. exact H.
Qed.

(****************************************************************)
(* Rend une liste de longueur n dont tous les elements sont x *)

Fixpoint list_const (n : nat) : bool -> BoolList :=

 (*****************)
 fun x : bool =>
 match n return (BoolList) with
 | O => nil
 | S n' => x :: list_const n' x
 end.

Lemma list_const_eq1 : forall x : bool, list_const 0 x = nil.
auto with arith. Qed.
Lemma list_const_eq2 :
 forall (n' : nat) (x : bool), list_const (S n') x = x :: list_const n' x.
auto with arith. Qed.

Lemma length_list_const :
 forall (n : nat) (x : bool), length (list_const n x) = n.
(**********************)
simple induction n. auto with arith. intros. simpl in |- *. auto with arith.
Qed.

(****************************************************************)
(* rev: renverse une liste *)

Fixpoint rev (l : BoolList) : BoolList :=

 (************************)
 match l return (BoolList) with
 | nil => nil
 | b :: l' => rev l' ++ b :: nil
 end.

Lemma rev_eq1 : rev nil = nil.
auto with arith. Qed.
Lemma rev_eq2 :
 forall (b : bool) (l' : BoolList), rev (b :: l') = rev l' ++ b :: nil.
auto with arith. Qed.


Lemma rev_eq : forall l n : BoolList, l = n -> rev l = rev n.
(***********)
intros; replace l with n; auto with arith.
Qed.

Lemma rev_app : forall l n : BoolList, rev (l ++ n) = rev n ++ rev l.
(************)
  simple induction l. intros. simpl. rewrite app_v_nil. auto.
  intros. simpl in |- *. rewrite H. apply app_assoc_r.
Qed.

Lemma rev_rev : forall l : BoolList, rev (rev l) = l.
(************)
simple induction l; auto with arith. intros; simpl in |- *. rewrite rev_app. rewrite H. auto with arith.
Qed.

Lemma length_rev : forall l : BoolList, length (rev l) = length l.
(***************)
simple induction l; auto with arith. intros. simpl in |- *.
rewrite length_app. simpl in |- *. rewrite Nat.add_1_r. rewrite H. trivial with arith.
Qed.

(****************************************************************)
(* map *)

Fixpoint map (l : BoolList) : (bool -> bool) -> BoolList :=

 (************************)
 fun f : bool -> bool =>
 match l return (BoolList ) with
 | nil => nil
 | b :: l' => f b :: map l' f
 end.


Lemma length_map :
 forall (l : BoolList) (f : bool -> bool), length (map l f) = length l.
simple induction l. auto with arith.
intros. simpl in |- *. rewrite H. trivial with arith.
Qed.

(****************************************************************)
(* Decidabilite *)

Lemma eq_cons :
 forall (l1 l2 : BoolList) (a1 a2 : bool), a1 :: l1 = a2 :: l2 -> l1 = l2.
intros.
change (tail (a1 :: l1) = tail (a2 :: l2)) in |- *.
apply (f_equal (A:=BoolList)).
exact H.
Qed.

(*
Lemma eq_cons2 : (l1,l2:(BoolList))(a1,a2:A)
		(cons a1 l1)=(cons a2 l2) -> a1=a2.
*)

Lemma not_eq_cons :
 forall (l1 l2 : BoolList) (a1 a2 : bool), l1 <> l2 -> a1 :: l1 <> a2 :: l2.
red in |- *. intros. absurd (l1 = l2). exact H.
apply (eq_cons l1 l2 a1 a2). exact H0.
Qed.

Axiom eq_list_dec : forall l m : BoolList, {l = m} + {l <> m}.

(*
(Induction l;Induction m). Auto with arith.
(Right;Discriminate).(Right;Discriminate). Intros.
*)

(* Adder.v *)

Definition BoolList_full_adder_sum :=
  (fix F (l : BoolList) : BoolList -> bool -> BoolList :=
     match l with
     | nil =>
         (fix F0 (l0 : BoolList) : bool -> BoolList :=
            match l0 with
            | nil => fun _ : bool => nil
            | cons b l1 =>
                fun z : bool =>
                cons (half_adder_sum b z) (F0 l1 (half_adder_carry b z))
            end)
     | cons b l0 =>
         fun x2 : BoolList =>
         match x2 with
         | nil =>
             fun y z : bool =>
             cons (half_adder_sum y z) (F l0 nil (half_adder_carry y z))
         | cons b0 l1 =>
             fun y z : bool =>
             cons (full_adder_sum y b0 z)
               (F l0 l1 (full_adder_carry y b0 z))
         end b
     end).


Lemma BoolList_full_adder_sum_eq1 :
 forall b : bool, BoolList_full_adder_sum nil nil b = nil.
Proof.
 auto.
Qed.

Lemma BoolList_full_adder_sum_eq2 :
 forall (vh : bool) (vt : BoolList) (b : bool),
 BoolList_full_adder_sum nil (vh :: vt) b =
 cons (half_adder_sum vh b)
   (BoolList_full_adder_sum nil vt (half_adder_carry vh b)).
Proof.
 auto.
Qed.

Lemma BoolList_full_adder_sum_eq3 :
 forall (vh : bool) (vt : BoolList) (b : bool),
 BoolList_full_adder_sum (vh :: vt) nil b =
 cons (half_adder_sum vh b)
   (BoolList_full_adder_sum vt nil (half_adder_carry vh b)).
Proof.
 auto.
Qed.

Lemma BoolList_full_adder_sum_eq4 :
 forall (vh : bool) (vt : BoolList) (wh : bool) (wt : BoolList) (b : bool),
 BoolList_full_adder_sum (vh :: vt) (wh :: wt) b =
 cons (full_adder_sum vh wh b)
   (BoolList_full_adder_sum vt wt (full_adder_carry vh wh b)).
Proof.
 auto.
Qed.


Definition BoolList_full_adder_carry :=
  (fix F (l : BoolList) : BoolList -> bool -> bool :=
     match l with
     | nil =>
         (fix F0 (l0 : BoolList) : bool -> bool :=
            match l0 with
            | nil => fun z : bool => z
            | cons b l1 => fun z : bool => F0 l1 (half_adder_carry b z)
            end)
     | cons b l0 =>
         fun x2 : BoolList =>
         match x2 with
         | nil => fun y z : bool => F l0 nil (half_adder_carry y z)
         | cons b0 l1 => fun y z : bool => F l0 l1 (full_adder_carry y b0 z)
         end b
     end).


Lemma BoolList_full_adder_carry_eq1 :
 forall b : bool, BoolList_full_adder_carry nil nil b = b.

Proof.
 auto.
Qed.

Lemma BoolList_full_adder_carry_eq2 :
 forall (vh : bool) (vt : BoolList) (b : bool),
 BoolList_full_adder_carry nil (vh :: vt) b =
 BoolList_full_adder_carry nil vt (half_adder_carry vh b).
Proof.
 auto.
Qed.


Lemma BoolList_full_adder_carry_eq3 :
 forall (vh : bool) (vt : BoolList) (b : bool),
 BoolList_full_adder_carry (vh :: vt) nil b =
 BoolList_full_adder_carry vt nil (half_adder_carry vh b).

Proof.
 auto.
Qed.

Lemma BoolList_full_adder_carry_eq4 :
 forall (vh : bool) (vt : BoolList) (wh : bool) (wt : BoolList) (b : bool),
 BoolList_full_adder_carry (vh :: vt) (wh :: wt) b =
 BoolList_full_adder_carry vt wt (full_adder_carry vh wh b).

Proof.
 auto.
Qed.


Definition BoolList_full_adder (v w : BoolList) (cin : bool) : BoolList :=
  app (BoolList_full_adder_sum v w cin)
    (cons (BoolList_full_adder_carry v w cin) nil).

(****************************************************************)

Lemma BoolList_full_adder_sum_v_nil_false :
 forall v : BoolList, BoolList_full_adder_sum v nil false = v.
simple induction v. trivial. intros.
rewrite BoolList_full_adder_sum_eq3. rewrite half_adder_carry_false.
rewrite half_adder_sum_false. rewrite H; auto.
Qed.

Lemma BoolList_full_adder_carry_v_nil_false :
 forall v : BoolList, BoolList_full_adder_carry v nil false = false.
simple induction v. trivial. intros.
rewrite BoolList_full_adder_carry_eq3. rewrite half_adder_carry_false.
trivial.
Qed.

Lemma BoolList_full_adder_sum_sym :
 forall (v w : BoolList) (cin : bool),
 BoolList_full_adder_sum v w cin = BoolList_full_adder_sum w v cin.
simple induction v. simple induction w. auto. intros.
rewrite BoolList_full_adder_sum_eq2. rewrite BoolList_full_adder_sum_eq3.
rewrite H. auto. simple induction w. intro.
rewrite BoolList_full_adder_sum_eq2. rewrite BoolList_full_adder_sum_eq3. rewrite H.
auto. intros. repeat rewrite BoolList_full_adder_sum_eq4. rewrite H.
do 2 rewrite full_adder_carry_sym1. do 2 rewrite full_adder_sum_sym1. auto.
Qed.

Lemma length_BoolList_full_adder_sum :
 forall (v w : BoolList) (cin : bool),
 length v = length w -> length (BoolList_full_adder_sum v w cin) = length v.
unfold length in |- *. simple induction v. simple induction w. intros. case cin. simpl in |- *. trivial.
simpl in |- *. trivial.
intros. absurd (length (nil:BoolList) = length (b :: b0)).
simpl in |- *. discriminate. exact H0. simple induction w. simpl in |- *. intros. discriminate H0.
intros. simpl in |- *. rewrite H. trivial. generalize H1. simpl in |- *. auto.
Qed.

Lemma BoolList_full_adder_carry_sym :
 forall (v w : BoolList) (cin : bool),
 BoolList_full_adder_carry v w cin = BoolList_full_adder_carry w v cin.
simple induction v. simple induction w. auto. intros.
rewrite BoolList_full_adder_carry_eq2. rewrite BoolList_full_adder_carry_eq3.
rewrite H; auto. simple induction w. intros. rewrite BoolList_full_adder_carry_eq2.
rewrite BoolList_full_adder_carry_eq3.
rewrite H. auto. intros. do 2 rewrite BoolList_full_adder_carry_eq4.
rewrite H. rewrite full_adder_carry_sym1. auto.
Qed.

Lemma BoolList_full_adder_sym :
 forall (v w : BoolList) (cin : bool),
 BoolList_full_adder v w cin = BoolList_full_adder w v cin.
unfold BoolList_full_adder in |- *.
intros.
rewrite BoolList_full_adder_sum_sym. rewrite BoolList_full_adder_carry_sym. auto.
Qed.

(* BV.v *)

Definition BoolList_null (n : nat) : BoolList := list_const n false.

Definition BoolListnot (v : BoolList) : BoolList := map v negb.

Fixpoint BoolList_to_nat (v : BoolList) : nat :=
  match v return nat with
  | nil => 0
  | cons b w => bool_to_nat b + (BoolList_to_nat w + BoolList_to_nat w)
  end.

Lemma BoolList_to_nat_app :
 forall (l n : BoolList) (ll : nat),
 (******************)
 length l = ll -> BoolList_to_nat (app l n) = BoolList_to_nat l + power2 ll * BoolList_to_nat n.
simple induction l. intros. inversion H. simpl in |- *. auto.
intros. simpl.
destruct ll.
inversion H0.
inversion H0.
rewrite (H n ll H2).
rewrite <- (plus_assoc (bool_to_nat b) (BoolList_to_nat b0 + BoolList_to_nat b0)).
f_equal.
rewrite <- plus_assoc.
rewrite <- (plus_assoc (BoolList_to_nat b0) (BoolList_to_nat b0)).
f_equal.
simpl.

rewrite mult_plus_distr_r. repeat rewrite plus_assoc.
subst.
rewrite <- plus_assoc.
rewrite Nat.add_comm.
reflexivity.
Qed.

Lemma BoolList_to_nat_app2 :
 forall l n : BoolList,
 (*******************)
 BoolList_to_nat (app l n) = BoolList_to_nat l + power2 (length l) * BoolList_to_nat n.
intros. apply BoolList_to_nat_app. auto.
Qed.

Lemma BoolList_null_nat : forall n : nat, BoolList_to_nat (BoolList_null n) = 0.
(****************)
unfold BoolList_null in |- *.
simple induction n; auto.
intros. simpl in |- *. rewrite H. auto.
Qed.

Lemma length_BV_null : forall n : nat, length (BoolList_null n) = n.
(*******************)
intro. apply length_list_const.
Qed.

(* AdderProof.v *)
Lemma BoolList_full_adder_nil_true_ok :
 forall v : BoolList, BoolList_to_nat (BoolList_full_adder v nil true) = S (BoolList_to_nat v).
simple induction v; auto with arith. unfold BoolList_full_adder in |- *. intros.
rewrite BoolList_full_adder_sum_eq3. rewrite BoolList_full_adder_carry_eq3.
rewrite app_eq2. rewrite half_adder_carry_true.
simpl in |- *. elim b. rewrite H. simpl in |- *. auto with arith.
rewrite BoolList_full_adder_sum_v_nil_false.
rewrite BoolList_full_adder_carry_v_nil_false. rewrite BoolList_to_nat_app2.
simpl in |- *. elim mult_n_O. elim plus_n_O. trivial with arith.
Qed.


Lemma BoolList_full_adder_nil_ok :
 forall (v : BoolList) (cin : bool),
 BoolList_to_nat (BoolList_full_adder v nil cin) = BoolList_to_nat v + bool_to_nat cin.

simple induction v. simple induction cin; auto with arith.
simple induction cin. rewrite BoolList_full_adder_nil_true_ok. simpl in |- *. rewrite Nat.add_1_r. reflexivity.
unfold BoolList_full_adder in |- *. rewrite BoolList_full_adder_sum_v_nil_false.
rewrite BoolList_full_adder_carry_v_nil_false. rewrite BoolList_to_nat_app2.
simpl in |- *. elim mult_n_O. elim plus_n_O. trivial with arith.
Qed.

(****************************************************************)

Require Import Lia.
Theorem BoolList_full_adder_ok :
 forall (v w : BoolList) (cin : bool),
 BoolList_to_nat (BoolList_full_adder v w cin) =
 BoolList_to_nat v + BoolList_to_nat w + bool_to_nat cin.
simple induction v.
intros.
rewrite BoolList_full_adder_sym.
simpl in |- *.
rewrite BoolList_full_adder_nil_ok.
auto with arith.

unfold BoolList_full_adder in |- *.
simple induction w.
rename b into a.
rename b0 into l.
simpl in |- *.
intro.
rewrite H.
simpl in |- *.
elim plus_n_O.
elim plus_n_O.
replace
 (BoolList_to_nat l + bool_to_nat (half_adder_carry a cin) +
  (BoolList_to_nat l + bool_to_nat (half_adder_carry a cin))) with
 (bool_to_nat (half_adder_carry a cin) + bool_to_nat (half_adder_carry a cin) +
  (BoolList_to_nat l + BoolList_to_nat l)).
repeat rewrite plus_assoc.
replace
 (bool_to_nat (half_adder_sum a cin) + bool_to_nat (half_adder_carry a cin) +
  bool_to_nat (half_adder_carry a cin)) with
 (bool_to_nat (half_adder_sum a cin) +
  (bool_to_nat (half_adder_carry a cin) +
   bool_to_nat (half_adder_carry a cin))).
rewrite half_adder_ok.
rewrite (plus_permute2 (bool_to_nat a) (bool_to_nat cin) (BoolList_to_nat l)).
rewrite
 (plus_permute2 (bool_to_nat a + BoolList_to_nat l) (bool_to_nat cin) (BoolList_to_nat l))
 .
trivial with arith.

trivial with arith.

repeat rewrite plus_assoc.
rewrite
 (plus_permute2 (bool_to_nat (half_adder_carry a cin))
    (bool_to_nat (half_adder_carry a cin)) (BoolList_to_nat l))
 .
rewrite (plus_comm (bool_to_nat (half_adder_carry a cin)) (BoolList_to_nat l)).
rewrite
 (plus_permute2 (BoolList_to_nat l + bool_to_nat (half_adder_carry a cin))
    (bool_to_nat (half_adder_carry a cin)) (BoolList_to_nat l))
 .
trivial with arith.

 rename b into a.
 rename b0 into l.
 intros a0 l0.
 intros.
simpl in |- *.
rewrite H.
clear H.
elim cin; elim a.
rewrite full_adder_carry_sym1.
rewrite full_adder_carry_true.
rewrite full_adder_sum_sym1.
rewrite full_adder_sum_true.
simpl in |- *.
repeat rewrite plus_n_SO.
elim plus_n_Sm.
elim plus_n_Sm.
simpl in |- *.
elim plus_n_Sm.
repeat rewrite plus_assoc.
lia.
(* rewrite *)
(*  (plus_permute2 (bool_to_nat a0 + BoolList_to_nat l) (BoolList_to_nat l0) (BoolList_to_nat l)) *)
(*  . *)
(* rewrite (plus_comm (bool_to_nat a0) (BoolList_to_nat l)). *)
(* rewrite (plus_permute2 (BoolList_to_nat l) (bool_to_nat a0) (BoolList_to_nat l)). *)
(* trivial with arith. *)

elim a0.
simpl in |- *.
elim plus_n_Sm.
simpl in |- *.
elim plus_n_O.
elim plus_n_Sm.
elim plus_n_Sm.
elim plus_n_Sm.
elim plus_n_O.
repeat rewrite plus_assoc.
rewrite (plus_permute2 (BoolList_to_nat l) (BoolList_to_nat l0) (BoolList_to_nat l)).
trivial with arith.

simpl in |- *.
repeat rewrite <- plus_n_Sm.
repeat rewrite <- plus_n_O.
repeat rewrite plus_assoc.
try trivial with arith.
rewrite (plus_permute2 (BoolList_to_nat l) (BoolList_to_nat l0) (BoolList_to_nat l)).
try trivial with arith.

elim a0.
simpl in |- *.
repeat rewrite <- plus_n_Sm.
repeat rewrite <- plus_n_O.
repeat rewrite plus_assoc.
simpl in |- *.
rewrite (plus_permute2 (BoolList_to_nat l) (BoolList_to_nat l0) (BoolList_to_nat l)).
trivial with arith.

simpl in |- *.
repeat rewrite <- plus_n_O.
repeat rewrite plus_assoc.
rewrite (plus_permute2 (BoolList_to_nat l) (BoolList_to_nat l0) (BoolList_to_nat l)).
trivial with arith.

elim a0; simpl in |- *; repeat rewrite <- plus_n_Sm;
 repeat rewrite <- plus_n_O; repeat rewrite plus_assoc;
 rewrite (plus_permute2 (BoolList_to_nat l) (BoolList_to_nat l0) (BoolList_to_nat l));
 trivial with arith.

Qed.

(* IncrDecr.v *)

Fixpoint BoolList_increment (l : BoolList) : BoolList  :=
  match l with
  | nil => nil
  | false :: v => true :: v
  | true :: v => false :: BoolList_increment v
  end.


Fixpoint BoolList_increment_carry (l : BoolList) : bool :=
  match l with
  | nil => true
  | false :: v => false
  | true :: v => BoolList_increment_carry v
  end.



Fixpoint BoolList_decrement (l : BoolList) : BoolList :=
  match l with
  | nil => nil
  | false :: v => true :: BoolList_decrement v
  | true :: v => false :: v
  end.

Fixpoint BoolList_decrement_carry (l : BoolList) : bool :=
  match l with
  | nil => true
  | false :: v => BoolList_decrement_carry v
  | true :: v => false
  end.



Lemma length_BoolList_increment :
 forall v : BoolList, length (BoolList_increment v) = length v.
simple induction v. auto.
simple induction b.
simpl in |- *. intros. rewrite H; trivial.
simpl in |- *. intros. trivial.
Qed.

Lemma length_BoolList_decrement :
 forall v : BoolList, length (BoolList_decrement v) = length v.
simple induction v. auto.
simple induction b.
simpl in |- *. intros. trivial.

simpl in |- *. intros. rewrite H; trivial.
Qed.

Lemma BoolList_increment_limit :
 forall n : nat,
 BoolList_increment (list_const n true) = list_const n false.
simple induction n. simpl in |- *. auto. intros. simpl in |- *. rewrite H; trivial.
Qed.

Lemma BoolList_decrement_limit :
 forall n : nat,
 BoolList_decrement (list_const n false) = list_const n true.
simple induction n. simpl in |- *. auto. intros. simpl in |- *. rewrite H; trivial.
Qed.


Lemma BoolList_increment_limit_carry :
 forall n : nat, BoolList_increment_carry (list_const n true) = true.
simple induction n. auto. intros. simpl in |- *. exact H.
Qed.

Lemma BoolList_decrement_limit_carry :
 forall n : nat, BoolList_decrement_carry (list_const n false) = true.
simple induction n. auto. intros. simpl in |- *. exact H.
Qed.


Lemma BoolList_increment_adder :
 forall v : BoolList,
 app (BoolList_increment v) (cons (BoolList_increment_carry v) nil) =
 BoolList_full_adder v nil true.
simple induction v.
simpl in |- *. unfold BoolList_full_adder in |- *. simpl in |- *. trivial.
(* Induction a. Unfold cons nil app . Simpl. Intros. Rewrite -> H.*)
simple induction b. intros. simpl in |- *.
rewrite H.
(* *)
unfold BoolList_full_adder in |- *. simpl in |- *. replace (half_adder_sum true true) with false.
trivial.
auto.
unfold BoolList_full_adder in |- *. intros. simpl in |- *.
replace (half_adder_sum false true) with true.
replace (BoolList_full_adder_sum b0 nil false) with b0.
replace (BoolList_full_adder_carry b0 nil false) with false.
trivial.
rewrite BoolList_full_adder_carry_v_nil_false. auto.
rewrite BoolList_full_adder_sum_v_nil_false. auto.
rewrite half_adder_sum_true. simpl. auto.
Qed.

Lemma BoolList_increment_ok :
 forall v : BoolList,
 BoolList_to_nat (app (BoolList_increment v) (cons (BoolList_increment_carry v) nil)) =
 S (BoolList_to_nat v).
intro. rewrite BoolList_increment_adder. rewrite BoolList_full_adder_ok.
simpl in |- *. elim plus_n_O. elim plus_n_Sm. auto.
Qed.

Lemma BoolList_decr_incr : forall v : BoolList, BoolList_decrement (BoolList_increment v) = v.
simple induction v. simpl in |- *. trivial.
simple induction b. intros. simpl in |- *. rewrite H; trivial.
intros. simpl in |- *. trivial.
Qed.

Lemma BoolList_incr_decr : forall v : BoolList, BoolList_increment (BoolList_decrement v) = v.
simple induction v.
auto. simple induction b; intros; simpl in |- *. trivial. rewrite H; trivial.
Qed.
(* Lists_fields.v *)

Fixpoint trunc (v : BoolList) : nat -> BoolList :=
  fun n : nat =>
  match v return BoolList with
  | nil => nil
  | b :: w =>
      match n return BoolList with
      | O => nil
      | S p => b :: trunc w p
      end
  end.

Definition strip (v : BoolList) (n : nat) :=
  rev (trunc (rev v) (length v - n)).

(* Selection d'une sous liste commencant a la position start, de
   longueur lengt *)
Definition sublist (v : BoolList) (start lengt : nat) :=
  trunc (strip v start) lengt.

(* Selection de la liste contenant le i-eme element d'une liste *)
Definition elemlist (v : BoolList) (i : nat) := trunc (strip v i) 1.

(****************************************************************)
(* lemmes sur trunc *)

Lemma length_trunc :
 forall (v : BoolList) (i : nat),
 (*****************)
 i <= length v -> length (trunc v i) = i.
simple induction v. simpl in |- *. auto with arith.
intros b b0 H. simple induction i. simpl in |- *. trivial with arith.
simpl in |- *. intros. apply eq_S. apply H. apply le_S_n. exact H1.
Qed.

Lemma trunc_inv :
 forall (v : BoolList) (i : nat) (b : bool),
 (**************)
 b :: trunc v i = trunc (b :: v) (S i).
simpl in |- *. trivial with arith.
Qed.

Lemma trunc_all : forall v : BoolList, trunc v (length v) = v.
(**************)
simple induction v. simpl in |- *. trivial with arith.
intros. rewrite length_eq2. simpl in |- *. rewrite H. trivial with arith.
Qed.

Lemma trunc_max :
 forall (v : BoolList) (i : nat),
 (**************)
 length v <= i -> trunc v i = v.
simple induction v. simpl in |- *. trivial with arith.
intros. inversion H0. rewrite trunc_all. trivial with arith.
simpl in |- *. rewrite H. trivial with arith.
apply le_Sn_le. generalize H1. simpl in |- *. trivial with arith.
Qed.

Lemma trunc_O : forall v : BoolList, trunc v 0 = nil.
(************)
simple induction v; auto with arith.
Qed.

Lemma le_length_trunc :
 forall (v : BoolList) (i : nat), length (trunc v i) <= i.
(********************)
simple induction v. simpl in |- *. auto with arith.
intros. case i. rewrite trunc_O. auto with arith.
intro. simpl in |- *. apply le_n_S. apply H.
Qed.

Lemma trunc_app :
 forall (v1 v2 : BoolList) (i : nat),
 (**************)
 trunc (v1 ++ v2) i = trunc v1 i ++ trunc v2 (i - length v1).
simple induction v1. simpl in |- *. auto with arith.
intros. rewrite app_eq2.
rewrite length_eq2. elim i. simpl in |- *. rewrite trunc_O. trivial with arith.
intros. simpl in |- *. rewrite H. trivial with arith.
Qed.

Lemma app_v_trunc :
 forall (v1 v2 : BoolList) (i : nat),
 (****************)
 v1 ++ trunc v2 i = trunc (v1 ++ v2) (length v1 + i).
intros. rewrite trunc_app. rewrite (trunc_max v1 (length v1 + i)).
replace (length v1 + i - length v1) with i. trivial with arith. auto with arith.
auto with arith.
Qed.

Lemma trunc_eq :
 forall (v1 v2 : BoolList) (i : nat), v1 = v2 -> trunc v1 i = trunc v2 i.
(*************)
intros. rewrite H. trivial with arith.
Qed.

Lemma trunc_sym :
 forall (v : BoolList) (i j : nat),
 (**************)
 trunc (trunc v i) j = trunc (trunc v j) i.
simple induction v. simpl in |- *. trivial with arith.
simple induction i; simple induction j. trivial with arith.
repeat rewrite trunc_O. simpl in |- *. trivial with arith.
repeat rewrite trunc_O. simpl in |- *. trivial with arith.
intros. simpl in |- *. rewrite H. trivial with arith.
Qed.

Lemma trunc_trunc1 :
 forall (v : BoolList) (i : nat),
 (*****************)
 trunc (trunc v i) i = trunc v i.
simple induction v. simpl in |- *. trivial with arith.
simple induction i. repeat rewrite trunc_O. trivial with arith.
intros. simpl in |- *. rewrite H. trivial with arith.
Qed.

Lemma trunc_trunc2 :
 forall (v : BoolList) (i j : nat),
 (*****************)
 i <= j -> trunc (trunc v i) j = trunc v i.
intros. rewrite (trunc_max (trunc v i) j). trivial with arith.
apply le_trans with i. apply le_length_trunc. exact H.
Qed.

Lemma trunc_trunc3 :
 forall (v : BoolList) (i j : nat),
 (*****************)
 j <= i -> trunc (trunc v i) j = trunc v j.
intros. rewrite <- (trunc_max (trunc v j) i). rewrite trunc_sym. trivial with arith.
apply le_trans with j. apply le_length_trunc.
exact H.
Qed.

Lemma trunc_plus_petit :
 forall (v1 v2 : BoolList) (i j : nat),
 (*********************)
 j <= i -> trunc v1 i = v2 -> trunc v1 j = trunc v2 j.
intros. rewrite <- H0. rewrite trunc_trunc3. trivial with arith. exact H.
Qed.

(****************************************************************)
(* lemmes sur strip *)

Lemma strip_nil : forall i : nat, strip nil i = nil.
(**************)
intro. auto with arith.
Qed.

Lemma strip_cons_S :
 forall (v : BoolList) (i : nat) (b : bool),
 (*****************)
 strip (b :: v) (S i) = strip v i.
unfold strip in |- *. simple induction i. simpl in |- *.
elim minus_n_O. intro. replace (length v) with (length (rev v)).
rewrite trunc_all. rewrite trunc_app. rewrite trunc_all.
elim minus_n_n. rewrite trunc_O. rewrite app_v_nil. trivial with arith.
apply length_rev.
intros. apply rev_eq. simpl in |- *.
rewrite trunc_app. rewrite length_rev. rewrite minus_minus_lem1.
rewrite trunc_O. rewrite app_v_nil. trivial with arith.
Qed.

Lemma length_strip :
 forall (v : BoolList) (i : nat),
 (*****************)
 i <= length v -> length (strip v i) = length v - i.
unfold strip in |- *. intros. rewrite length_rev. rewrite length_trunc. trivial with arith.
rewrite length_rev. apply minus_le_lem2.
Qed.

Lemma le_length_strip :
 forall (v : BoolList) (i : nat),
 (********************)
 length (strip v i) <= length v - i.
unfold strip in |- *. intros. rewrite length_rev. apply le_length_trunc.
Qed.

Lemma strip_inv :
 forall (v : BoolList) (i : nat),
 (***************)
 rev (trunc (rev v) (length v - i)) = strip v i.
unfold strip in |- *. trivial with arith.
Qed.

Lemma strip_all : forall v : BoolList, strip v (length v) = nil.
(**************)
unfold strip in |- *. intro. rewrite <- minus_n_n. rewrite trunc_O. auto with arith.
Qed.

Lemma strip_max :
 forall (v : BoolList) (i : nat),
 (**************)
 length v <= i -> strip v i = nil.
unfold strip in |- *. intros. rewrite <- rev_eq1.
apply rev_eq. rewrite <- length_rev. rewrite minus_le_O. rewrite trunc_O. auto.
rewrite length_rev. exact H.
Qed.

Lemma strip_O : forall v : BoolList, strip v 0 = v.
(************)
intro. unfold strip in |- *. rewrite <- minus_n_O. rewrite <- length_rev.
rewrite trunc_all. rewrite rev_rev. trivial with arith.
Qed.

Lemma strip_app :
 forall (v1 v2 : BoolList) (i : nat),
 (**************)
 strip (v1 ++ v2) i = strip v1 i ++ strip v2 (i - length v1).
simple induction v1. simpl in |- *. intros. elim minus_n_O. trivial with arith.
simple induction v2. intro. simpl in |- *.
rewrite strip_nil. rewrite app_v_nil. rewrite app_v_nil. trivial with arith.
simple induction i.
rewrite strip_O. simpl in |- *. rewrite strip_O. rewrite strip_O. auto with arith.
intros. rewrite app_eq2. rewrite strip_cons_S.
rewrite strip_cons_S. rewrite length_eq2. simpl in |- *. apply H.
Qed.

Lemma strip_strip_S :
 forall (v : BoolList) (i j : nat),
 (******************)
 strip (strip v (S i)) j = strip (strip v i) (S j).
simple induction v. intros. rewrite strip_nil. rewrite strip_nil. trivial with arith.
simple induction i. intros. rewrite strip_O.
do 2 rewrite strip_cons_S. rewrite strip_O. trivial with arith.
simple induction j. rewrite strip_O.
repeat rewrite strip_cons_S. elim n. rewrite strip_O. trivial with arith.
intros. rewrite <- H. rewrite strip_O. trivial with arith.
intros. do 2 rewrite strip_cons_S. apply H.
Qed.

Lemma strip_sym :
 forall (v : BoolList) (i j : nat),
 (**************)
 strip (strip v i) j = strip (strip v j) i.
simple induction v. intros. rewrite strip_nil. rewrite strip_nil. trivial with arith.
simple induction i. intro. rewrite strip_O. rewrite strip_O. trivial with arith.
simple induction j. rewrite strip_O. rewrite strip_O. try trivial with arith.
intros. rewrite strip_cons_S. rewrite strip_cons_S.
replace (strip (strip b0 n) (S n0)) with (strip (strip b0 (S n)) n0).
apply H. apply strip_strip_S.
Qed.

Lemma strip_eq :
 forall (v1 v2 : BoolList) (i : nat), v1 = v2 -> strip v1 i = strip v2 i.
(*************)
intros. rewrite H. trivial with arith.
Qed.

Lemma strip_strip :
 forall (v : BoolList) (i j : nat),
 (****************)
 strip (strip v i) j = strip v (i + j).
simple induction v. intros. rewrite strip_nil. rewrite strip_nil. trivial with arith.
simple induction i. intro. simpl in |- *. rewrite strip_O. trivial with arith.
simple induction j. rewrite strip_O. elim plus_n_O. trivial with arith.
intros. rewrite strip_cons_S. simpl in |- *. rewrite strip_cons_S. apply H.
Qed.

(****************************************************************)
(* lemmes sur trunc et strip ensembles *)

Lemma app_trunc_strip :
 forall (v : BoolList) (i : nat),
 (********************)
 trunc v i ++ strip v i = v.
simple induction v. unfold strip in |- *. simpl in |- *. trivial with arith.
intros. elim i. rewrite trunc_O. rewrite strip_O. simpl in |- *. trivial with arith.
intros. unfold strip in |- *. simpl in |- *.
rewrite trunc_app. rewrite rev_app. rewrite length_rev.
case n. rewrite <- minus_n_O.
rewrite <- minus_n_n. rewrite trunc_O. rewrite trunc_O. simpl in |- *.
rewrite <- length_rev. rewrite trunc_all. rewrite rev_rev. trivial with arith.
intro. replace (length b0 - S n0 - length b0) with 0.
rewrite trunc_O. simpl in |- *.
replace (rev (trunc (rev b0) (length b0 - S n0))) with (strip b0 (S n0)).
rewrite H. trivial with arith.
unfold strip in |- *. trivial with arith.
rewrite minus_minus_lem1. trivial with arith.
Qed.

Lemma strip_trunc_i :
 forall (v : BoolList) (i : nat), strip (trunc v i) i = nil.
(******************)
simple induction v. auto with arith.
simple induction i. auto with arith.
intros. simpl in |- *. rewrite strip_cons_S. apply H.
Qed.

Lemma strip_trunc :
 forall (v : BoolList) (i j : nat),
 (****************)
 strip (trunc v i) j = trunc (strip v j) (i - j).
simple induction v. simpl in |- *. unfold strip in |- *. simpl in |- *. trivial with arith.
simple induction i; simple induction j.
simpl in |- *. rewrite strip_O. rewrite trunc_O. trivial with arith.
rewrite trunc_O.
simpl in |- *. intros. unfold strip in |- *. simpl in |- *. rewrite trunc_O. trivial with arith.
rewrite strip_O. rewrite strip_O. elim minus_n_O. trivial with arith.
intros. rewrite strip_cons_S. simpl in |- *. rewrite strip_cons_S. apply H.
Qed.

Lemma trunc_strip :
 forall (v : BoolList) (i j : nat),
 (****************)
 trunc (strip v i) j = strip (trunc v (i + j)) i.
simple induction v. unfold strip in |- *. simpl in |- *. trivial with arith.
simple induction i; simple induction j. rewrite trunc_O. rewrite strip_O. auto with arith.
intros. rewrite strip_O. rewrite strip_O. auto with arith.
rewrite trunc_O. elim plus_n_O. rewrite strip_trunc_i. trivial with arith.
intros.
rewrite strip_cons_S. replace (S n + S n0) with (S (n + S n0)).
simpl in |- *. rewrite strip_cons_S. apply H.
auto with arith.
Qed.

(****************************************************************)
(* lemmes sur elemlist et sublist *)

Lemma elemlist_is_sublist :
 forall (v : BoolList) (i : nat),
 (************************)
 elemlist v i = sublist v i 1.
unfold elemlist, sublist in |- *. trivial with arith.
Qed.

Lemma elemlist_cons_S :
 forall (v : BoolList) (i : nat) (b : bool),
 (********************)
 elemlist (b :: v) (S i) = elemlist v i.
unfold elemlist in |- *. intros. rewrite strip_cons_S. trivial with arith.
Qed.

Lemma elemlist_cons_O :
 forall (v : BoolList) (b : bool),
 (********************)
 elemlist (b :: v) 0 = b :: nil.
intros.
unfold elemlist in |- *. rewrite strip_O. simpl in |- *. rewrite trunc_O. trivial with arith.
Qed.

Lemma elemlist_inv :
 forall (l : BoolList) (i : nat),
 (*****************)
 trunc (strip l i) 1 = elemlist l i.
unfold elemlist in |- *. trivial with arith.
Qed.

Lemma app_trunc_elemlist :
 forall (v : BoolList) (i : nat),
 (***********************)
 S i <= length v -> trunc v i ++ elemlist v i = trunc v (S i).
simple induction v. unfold elemlist in |- *. simpl in |- *. trivial with arith.
simple induction i. simpl in |- *. unfold elemlist in |- *. rewrite trunc_O.
rewrite strip_O. simpl in |- *. rewrite trunc_O. trivial with arith.
intros. simpl in |- *. unfold elemlist in |- *.
rewrite strip_cons_S. unfold elemlist in H. rewrite H. trivial with arith.
generalize H1. simpl in |- *. auto with arith.
Qed.


Lemma length_elemlist :
 forall (l : BoolList) (i : nat),
 (********************)
 i < length l -> length (elemlist l i) = 1.
intros. unfold elemlist in |- *. rewrite length_trunc. trivial with arith.
rewrite length_strip. inversion H. rewrite <- minus_Sn_m. auto with arith. auto with arith.
rewrite <- minus_Sn_m. auto with arith. apply le_Sn_le. exact H1. apply lt_le_weak. exact H.
Qed.

(* Lists_replace.v *)


(* Remplace l'element de l a la position par new *)
Fixpoint replace (l : BoolList) : nat -> bool -> BoolList :=
  fun (position : nat) (new : bool) =>
  match l return (BoolList) with
  | nil =>
      (* nil *)  nil
  | x :: l' =>
      (* (cons x l') *)
      match position return (BoolList) with
      | O =>
          (* O *)  new :: l'
          (* (S n') *)
      | S n' => x :: replace l' n' new
      end
  end.

Lemma replace_ok :
 forall (l : BoolList) (i : nat) (x : bool),
 (***************)
 i < length l -> elemlist (replace l i x) i = x :: nil.
simple induction l. simpl in |- *. intros. absurd (i < 0). apply lt_n_O.
exact H.
simple induction i. intros. simpl in |- *.
unfold elemlist in |- *. rewrite strip_O. simpl in |- *. rewrite trunc_O; trivial with arith.
intros. simpl in |- *. clear H0. unfold elemlist in |- *. rewrite strip_cons_S.
rewrite elemlist_inv.
apply H. apply lt_S_n. generalize H1. simpl in |- *. trivial with arith.
Qed.

(* On montre que tous les elements, sauf celui que l'on remplace,
   ne sont pas modifies: *)
Lemma replace_keep_others :
 forall (l : BoolList) (i p : nat) (x : bool),
 (************************)
 i < length l ->
 p < length l -> i <> p -> elemlist (replace l p x) i = elemlist l i.
simple induction l. simpl in |- *. intros. absurd (i < 0). apply lt_n_O.
exact H.
simple induction i.
intros. unfold elemlist in |- *. rewrite elemlist_inv. rewrite elemlist_inv.
generalize H1 H2. elim p. intros. absurd (0 <> 0). unfold not in |- *; auto with arith.
exact H4.
intros. simpl in |- *. rewrite elemlist_cons_O. rewrite elemlist_cons_O. trivial with arith.
simple induction p. intros. simpl in |- *.
rewrite elemlist_cons_S. rewrite elemlist_cons_S. trivial with arith.
intros. clear H1. simpl in |- *. do 2 rewrite elemlist_cons_S.
clear H0. apply H. apply lt_S_n. generalize H2; simpl in |- *; trivial with arith.
apply lt_S_n. generalize H3; simpl in |- *; trivial with arith.
generalize H4. red in |- *. auto with arith.
Qed.

Lemma length_replace :
 forall (l : BoolList) (p : nat) (x : bool),
 (*******************)
 p < length l -> length (replace l p x) = length l.
simple induction l. simpl in |- *. try trivial with arith.
simple induction p. intros. simpl in |- *. apply eq_S. try trivial with arith.
intros. clear H0. simpl in |- *. rewrite H. try trivial with arith.
auto with arith.
Qed.

Lemma replace_sym :
 forall (l : BoolList) (p p' : nat) (x x' : bool),
 (****************)
 p < length l ->
 p' < length l ->
 p <> p' -> replace (replace l p' x') p x = replace (replace l p x) p' x'.
simple induction l. simpl in |- *. trivial with arith.
simple induction p. intros. generalize H1 H2.
elim p'. intros. absurd (0 <> 0); unfold not in |- *; auto with arith.
intros. simpl in |- *. trivial with arith.
simple induction p'. intros. simpl in |- *. trivial with arith.
intros. clear H1. clear H0. simpl in |- *. rewrite H. trivial with arith.
auto with arith.
auto with arith.
red in |- *. auto with arith.
Qed.

Lemma replace_newer :
 forall (l : BoolList) (p : nat) (x x' : bool),
 (*****************)
 p < length l -> replace (replace l p x) p x' = replace l p x'.
simple induction l. simpl in |- *. trivial with arith.
simple induction p. simpl in |- *. intros. trivial with arith.
intros. clear H0. simpl in |- *. rewrite H. trivial with arith.
auto with arith.
Qed.

(* GENE/Memo.v *)

Inductive Memo : Type :=
| nil2d : Memo
| cons2d : BoolList-> Memo -> Memo.

Definition length2d : Memo -> nat :=
  fix length2d l :=
  match l with
   | nil2d => O
   | cons2d _  l' => S (length2d l')
  end.

Fixpoint list_const2d (n : nat) : BoolList -> Memo :=

 (*****************)
 fun x : BoolList =>
 match n return (Memo) with
 | O => nil2d
 | S n' => cons2d x (list_const2d n' x)
 end.

(* Une memoire de taille donnee, initialisee avec un certain BV *)
Definition MemoEmpty (n : nat) (v : BoolList) : Memo := list_const2d n v.

Fixpoint trunc2d (v : Memo) : nat -> Memo :=
  fun n : nat =>
  match v return Memo with
  | nil2d => nil2d
  | cons2d b w =>
      match n return Memo with
      | O => nil2d
      | S p => cons2d b (trunc2d w p)
      end
  end.

Definition app2d : Memo -> Memo -> Memo :=
  fix app l m :=
  match l with
   | nil2d => m
   | cons2d a  l1 => cons2d a (app l1 m)
  end.

Fixpoint rev2d (l : Memo) : Memo :=

 (************************)
 match l return (Memo) with
 | nil2d => nil2d
 | cons2d b l' => app2d (rev2d l') (cons2d b nil2d)
 end.

Definition strip2d (v : Memo) (n : nat) :=
  rev2d (trunc2d (rev2d v) (length2d v - n)).

Definition MemoZone (v : Memo ) (start lengt : nat) :=
  trunc2d (strip2d v start) lengt.

Definition MemoRead (v : Memo) (i : nat) := trunc2d (strip2d v i) 1.

(* Remplace l'element de l a la position par new *)
Fixpoint MemoWrite (l : Memo) : nat -> BoolList -> Memo :=
  fun (position : nat) (new : BoolList) =>
  match l return (Memo) with
  | nil2d =>
      (* nil *)  nil2d
  | cons2d x l' =>
      (* (cons x l') *)
      match position return (Memo) with
      | O =>
          (* O *)  cons2d new l'
          (* (S n') *)
      | S n' => cons2d x (MemoWrite l' n' new)
      end
  end.

(* Adresse OK si elle est strictement inferieure a la taille de la memoire *)
Definition AddrOK (m : Memo) (a : nat) : Prop := a < length2d m.

Definition MMemo (v : BoolList) : Memo := cons2d v nil2d.
(* Cree une memoire d'un seul BV. C'est a utiliser avec MemoRead car MemoRead
ne rend pas un BV mais une memoire. Il faudrait definir "car" *)

Lemma length2d_app :
 forall v1 v2 : Memo,
 (***************)
 length2d (app2d v1 v2) = length2d v1 + length2d v2.
simple induction v1. simpl in |- *. trivial with arith.
intros. simpl in |- *. rewrite H. trivial with arith.
Qed.

Lemma length2d_rev : forall l : Memo, length2d (rev2d l) = length2d l.
(***************)
simple induction l; auto with arith. intros. simpl in |- *.
rewrite length2d_app. simpl in |- *. rewrite Nat.add_1_r. rewrite H. trivial with arith.
Qed.

Lemma length2d_eq2 :
 forall (x : BoolList) (l : Memo), length2d (cons2d x l) = S (length2d l).
  auto with arith. Qed.

Lemma trunc2d_all : forall v : Memo, trunc2d v (length2d v) = v.
(**************)
simple induction v. simpl in |- *. trivial with arith.
intros. rewrite length2d_eq2. simpl in |- *. rewrite H. trivial with arith.
Qed.

Lemma app2d_nil_end : forall l:Memo, l = app2d l nil2d.
Proof.
        induction l; simpl in |- *; auto.
        rewrite <- IHl; auto.
Qed.

Lemma app2d_v_nil : forall v : Memo, app2d v nil2d = v.
(**************)
intro.
rewrite <- app2d_nil_end; trivial with arith.
Qed.

Lemma app2d_assoc_r : forall l m n:Memo, app2d (app2d l m) n = app2d l (app2d m n).
Proof.
  intros. induction l; simpl in |- *; auto.
  rewrite <- IHl. auto.
Qed.

Lemma rev2d_app : forall l n : Memo, rev2d (app2d l n) = app2d (rev2d n) (rev2d l).
(************)
  simple induction l. intros. simpl. rewrite app2d_v_nil. auto.
  intros. simpl in |- *. rewrite H. apply app2d_assoc_r.
Qed.

Lemma rev2d_rev2d : forall l : Memo, rev2d (rev2d l) = l.
(************)
simple induction l; auto with arith. intros; simpl in |- *. rewrite rev2d_app. rewrite H. auto with arith.
Qed.

Lemma strip2d_O : forall v : Memo, strip2d v 0 = v.
(************)
intro. unfold strip2d in |- *. rewrite <- minus_n_O. rewrite <- length2d_rev.
rewrite trunc2d_all. rewrite rev2d_rev2d. trivial with arith.
Qed.

Lemma trunc2d_O : forall v : Memo, trunc2d v 0 = nil2d.
(************)
simple induction v; auto with arith.
Qed.

Lemma app2d_eq2 : forall (x : BoolList) (l l' : Memo), app2d (cons2d x l) l' = cons2d x (app2d l l').
  auto with arith. Qed.

Lemma trunc2d_app :
 forall (v1 v2 : Memo) (i : nat),
 (**************)
 trunc2d (app2d v1 v2) i = app2d (trunc2d v1 i) (trunc2d v2 (i - length2d v1)).
simple induction v1. simpl in |- *. auto with arith.
intros. rewrite app2d_eq2.
rewrite length2d_eq2. elim i. simpl in |- *. rewrite trunc2d_O. trivial with arith.
intros. simpl in |- *. rewrite H. trivial with arith.
Qed.

Lemma rev2d_eq : forall l n : Memo, l = n -> rev2d l = rev2d n.
(***********)
intros; replace l with n; auto with arith.
Qed.

Lemma strip2d_cons_S :
 forall (v : Memo) (i : nat) (b : BoolList),
 (*****************)
 strip2d (cons2d b v) (S i) = strip2d v i.
unfold strip2d in |- *. simple induction i. simpl in |- *.
elim minus_n_O. intro. replace (length2d v) with (length2d (rev2d v)).
rewrite trunc2d_all. rewrite trunc2d_app. rewrite trunc2d_all.
elim minus_n_n. rewrite trunc2d_O. rewrite app2d_v_nil. trivial with arith.
apply length2d_rev.
intros. apply rev2d_eq. simpl in |- *.
rewrite trunc2d_app. rewrite length2d_rev. rewrite minus_minus_lem1.
rewrite trunc2d_O. rewrite app2d_v_nil. trivial with arith.
Qed.

Lemma MemoRead_inv :
 forall (l : Memo) (i : nat),
 (*****************)
 trunc2d (strip2d l i) 1 = MemoRead l i.
unfold elemlist in |- *. trivial with arith.
Qed.

Lemma replace2d_ok :
 forall (l : Memo) (i : nat) (x : BoolList),
 (***************)
 i < length2d l -> MemoRead (MemoWrite l i x) i = cons2d x nil2d.
simple induction l. simpl in |- *. intros. absurd (i < 0). apply lt_n_O.
exact H.
simple induction i. intros. simpl in |- *.
unfold MemoRead in |- *. rewrite strip2d_O. simpl in |- *. rewrite trunc2d_O; trivial with arith.
intros. simpl in |- *. clear H0. unfold MemoRead in |- *. rewrite strip2d_cons_S.
rewrite MemoRead_inv.
apply H. apply lt_S_n. simpl in H1. assumption.
Qed.

Lemma read_write :
 forall (m : Memo) (a : nat) (v : BoolList),
 AddrOK m a -> MemoRead (MemoWrite m a v) a = MMemo v.
intros. apply replace2d_ok; auto.
Qed.

(********************************************************************)

(* BLOCK/Fill_defs.v *)


Fixpoint IsNull (v : BoolList) : bool :=
  match v return bool with
  | nil => true
  | b :: w =>
      match b return bool with
      | true => false
      | false => IsNull w
      end
  end.

Lemma IsNull_nil : IsNull nil = true.
auto.
Qed.

Lemma IsNull_false :
 forall (a : bool) (v : BoolList), IsNull (cons a v) = true -> a = false.
simple induction a. simpl in |- *. auto. trivial.
Qed.

Lemma IsNull_cons :
 forall (a : bool) (v : BoolList), IsNull (cons a v) = true -> IsNull v = true.
simple induction a. simpl in |- *. intros. absurd (false = true).
auto. exact H. intros v. auto.
Qed.

Lemma IsNull_null : forall n : nat, IsNull (BoolList_null n) = true.
simple induction n. simpl in |- *. trivial.
intros. simpl in |- *. exact H.
Qed.

Lemma IsNull_BV_null :
 forall v : BoolList, IsNull v = true -> v = BoolList_null (length v).
simple induction v. simpl in |- *. unfold BoolList_null in |- *. auto.
intros a l H. intro.
change (a :: l = false :: BoolList_null (length l)) in |- *.
rewrite <- H. generalize H0. replace a with false. trivial.
symmetry  in |- *. apply IsNull_false with (v := l). exact H0.
apply IsNull_cons with (a := a). exact H0.
Qed.

(* BLOCK/Fill_spec.v *)


Fixpoint di (st : nat) : BoolList -> BoolList -> BoolList -> Memo -> BoolList :=
  fun (di0 cx0 al0 : BoolList) (mem0 : Memo) =>
  match st return BoolList with
  | O => di0
  | S t =>
      match IsNull (cx t di0 cx0 al0 mem0) return BoolList with
      | true => di t di0 cx0 al0 mem0
      | false => BoolList_increment (di t di0 cx0 al0 mem0)
      end
  end

 with cx (st : nat) : BoolList -> BoolList -> BoolList -> Memo -> BoolList :=
  fun (di0 cx0 al0 : BoolList) (mem0 : Memo) =>
  match st return BoolList with
  | O => cx0
  | S t =>
      match IsNull (cx t di0 cx0 al0 mem0) return BoolList with
      | true => cx t di0 cx0 al0 mem0
      | false => BoolList_decrement (cx t di0 cx0 al0 mem0)
      end
  end

 with al (st : nat) : BoolList -> BoolList -> BoolList -> Memo -> BoolList :=
  fun (di0 cx0 al0 : BoolList) (mem0 : Memo) =>
  match st return BoolList with
  | O => al0
  | S t =>
      match IsNull (cx t di0 cx0 al0 mem0) return BoolList with
      | true => al t di0 cx0 al0 mem0
      | false => al t di0 cx0 al0 mem0
      end
  end

 with mem (st : nat) : BoolList -> BoolList -> BoolList -> Memo -> Memo :=
  fun (di0 cx0 al0 : BoolList) (mem0 : Memo) =>
  match st return Memo with
  | O => mem0
  | S t =>
      match IsNull (cx t di0 cx0 al0 mem0) return Memo with
      | true => mem t di0 cx0 al0 mem0
      | false =>
          MemoWrite (mem t di0 cx0 al0 mem0)
            (BoolList_to_nat (di t di0 cx0 al0 mem0)) (al t di0 cx0 al0 mem0)
      end
  end.

Lemma di_t :
 forall (t : nat) (di0 cx0 al0 : BoolList) (mem0 : Memo),
 di (S t) di0 cx0 al0 mem0 =
 match IsNull (cx t di0 cx0 al0 mem0) return BoolList with
 | true => di t di0 cx0 al0 mem0
 | false => BoolList_increment (di t di0 cx0 al0 mem0)
 end.
auto.
Qed.

Lemma cx_t :
 forall (t : nat) (di0 cx0 al0 : BoolList) (mem0 : Memo),
 cx (S t) di0 cx0 al0 mem0 =
 match IsNull (cx t di0 cx0 al0 mem0) return BoolList with
 | true => cx t di0 cx0 al0 mem0
 | false => BoolList_decrement (cx t di0 cx0 al0 mem0)
 end.
auto.
Qed.

Lemma al_t :
 forall (t : nat) (di0 cx0 al0 : BoolList) (mem0 : Memo),
 al (S t) di0 cx0 al0 mem0 =
 match IsNull (cx t di0 cx0 al0 mem0) return BoolList with
 | true => al t di0 cx0 al0 mem0
 | false => al t di0 cx0 al0 mem0
 end.
auto.
Qed.

Lemma al_constant :
 forall (t : nat) (di0 cx0 al0 : BoolList) (mem0 : Memo),
 al t di0 cx0 al0 mem0 = al0.
simple induction t. auto.
intros. rewrite al_t. elim (IsNull (cx n di0 cx0 al0 mem0)). apply H. apply H.
Qed.

Lemma mem_t :
 forall (t : nat) (di0 cx0 al0 : BoolList) (mem0 : Memo),
 mem (S t) di0 cx0 al0 mem0 =
 match IsNull (cx t di0 cx0 al0 mem0) return Memo with
 | true => mem t di0 cx0 al0 mem0
 | false =>
     MemoWrite (mem t di0 cx0 al0 mem0) (BoolList_to_nat (di t di0 cx0 al0 mem0))
       (al t di0 cx0 al0 mem0)
 end.
auto.
Qed.
(****************************************************************)
(* Longueurs des registres *)

Lemma length_di :
 forall (a_size: nat) (di_init: BoolList) (cx_init: BoolList) (al_init: BoolList) (mem_init: Memo) (di_initsize: length di_init = a_size) (t : nat), length (di t di_init cx_init al_init mem_init) = a_size.
simple induction t. simpl in |- *. exact di_initsize.
intros.
rewrite di_t. elim (IsNull (cx n di_init cx_init al_init mem_init)). exact H.
rewrite length_BoolList_increment. exact H.
Qed.

Lemma length_cx :
  forall (a_size: nat)
         (di_init cx_init al_init: BoolList) (mem_init: Memo)
         (cx_initsize: length cx_init = a_size)
         (t : nat), length (cx t di_init cx_init al_init mem_init) = a_size.
simple induction t. simpl in |- *. exact cx_initsize.
intros.
rewrite cx_t. elim (IsNull (cx n di_init cx_init al_init mem_init)). exact H.
rewrite length_BoolList_decrement. exact H.
Qed.

Lemma length_al :
  forall (d_size: nat)
         (di_init cx_init al_init: BoolList) (mem_init: Memo)
         (al_initsize: length al_init = d_size)
         (t : nat), length (al t di_init cx_init al_init mem_init) = d_size.
intros. rewrite al_constant. exact al_initsize.
Qed.

(* BLOCK/Fill_impl.v *)


(****************************************************************)
(* Implementation *)

(* seq1 *)

Definition di1 (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList) := di0.
Definition cx1 (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList) := cx0.
Definition al1 (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList) := al0.
Definition mem1 (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList) := mem0.
Definition ad1 (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList) := di0.
Definition da1 (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList) := al0.

(* seq2 *)

Fixpoint di2 (st : nat) : BoolList -> BoolList -> BoolList -> Memo -> BoolList -> BoolList -> BoolList :=
  fun (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList) =>
  match st return BoolList with
  | O => di0
  | S t =>
      match IsNull (cx2 t di0 cx0 al0 mem0 ad0 da0) return BoolList with
      | true => di2 t di0 cx0 al0 mem0 ad0 da0
      | false => di2 t di0 cx0 al0 mem0 ad0 da0
      end
  end

 with cx2 (st : nat) : BoolList -> BoolList -> BoolList -> Memo -> BoolList -> BoolList -> BoolList :=
  fun (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList) =>
  match st return BoolList with
  | O => cx0
  | S t =>
      match IsNull (cx2 t di0 cx0 al0 mem0 ad0 da0) return BoolList with
      | true => cx2 t di0 cx0 al0 mem0 ad0 da0
      | false => BoolList_decrement (cx2 t di0 cx0 al0 mem0 ad0 da0)
      end
  end

 with al2 (st : nat) : BoolList -> BoolList -> BoolList -> Memo -> BoolList -> BoolList -> BoolList :=
  fun (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList) =>
  match st return BoolList with
  | O => al0
  | S t =>
      match IsNull (cx2 t di0 cx0 al0 mem0 ad0 da0) return BoolList with
      | true => al2 t di0 cx0 al0 mem0 ad0 da0
      | false => al2 t di0 cx0 al0 mem0 ad0 da0
      end
  end

 with mem2 (st : nat) : BoolList -> BoolList -> BoolList -> Memo -> BoolList -> BoolList -> Memo :=
  fun (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList) =>
  match st return Memo with
  | O => mem0
  | S t =>
      match IsNull (cx2 t di0 cx0 al0 mem0 ad0 da0) return Memo with
      | true => mem2 t di0 cx0 al0 mem0 ad0 da0
      | false =>
          MemoWrite (mem2 t di0 cx0 al0 mem0 ad0 da0)
            (BoolList_to_nat (ad2 t di0 cx0 al0 mem0 ad0 da0))
            (da2 t di0 cx0 al0 mem0 ad0 da0)
      end
  end

 with ad2 (st : nat) : BoolList -> BoolList -> BoolList -> Memo -> BoolList -> BoolList -> BoolList :=
  fun (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList) =>
  match st return BoolList with
  | O => ad0
  | S t =>
      match IsNull (cx2 t di0 cx0 al0 mem0 ad0 da0) return BoolList with
      | true => ad2 t di0 cx0 al0 mem0 ad0 da0
      | false => BoolList_increment (ad2 t di0 cx0 al0 mem0 ad0 da0)
      end
  end

 with da2 (st : nat) : BoolList -> BoolList -> BoolList -> Memo -> BoolList -> BoolList -> BoolList :=
  fun (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList) =>
  match st return BoolList with
  | O => da0
  | S t =>
      match IsNull (cx2 t di0 cx0 al0 mem0 ad0 da0) return BoolList with
      | true => da2 t di0 cx0 al0 mem0 ad0 da0
      | false => da2 t di0 cx0 al0 mem0 ad0 da0
      end
  end.

Lemma di2_t :
 forall (t : nat) (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList),
 di2 (S t) di0 cx0 al0 mem0 ad0 da0 =
 match IsNull (cx2 t di0 cx0 al0 mem0 ad0 da0) return BoolList with
 | true => di2 t di0 cx0 al0 mem0 ad0 da0
 | false => di2 t di0 cx0 al0 mem0 ad0 da0
 end.
auto.
Qed.

Lemma di2_constant :
 forall (t : nat) (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList),
 di2 t di0 cx0 al0 mem0 ad0 da0 = di0.
simple induction t. simpl in |- *; trivial.
intros. rewrite di2_t. elim (IsNull (cx2 n di0 cx0 al0 mem0 ad0 da0)). apply H.
apply H.
Qed.

Lemma cx2_t :
 forall (t : nat) (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList),
 cx2 (S t) di0 cx0 al0 mem0 ad0 da0 =
 match IsNull (cx2 t di0 cx0 al0 mem0 ad0 da0) return BoolList with
 | true => cx2 t di0 cx0 al0 mem0 ad0 da0
 | false => BoolList_decrement (cx2 t di0 cx0 al0 mem0 ad0 da0)
 end.
auto.
Qed.

Lemma al2_t :
 forall (t : nat) (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList),
 al2 (S t) di0 cx0 al0 mem0 ad0 da0 =
 match IsNull (cx2 t di0 cx0 al0 mem0 ad0 da0) return BoolList with
 | true => al2 t di0 cx0 al0 mem0 ad0 da0
 | false => al2 t di0 cx0 al0 mem0 ad0 da0
 end.
auto.
Qed.

Lemma al2_constant :
 forall (t : nat) (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList),
 al2 t di0 cx0 al0 mem0 ad0 da0 = al0.
simple induction t. simpl in |- *; trivial.
intros. rewrite al2_t. elim (IsNull (cx2 n di0 cx0 al0 mem0 ad0 da0)). apply H.
apply H.
Qed.

Lemma mem2_t :
 forall (t : nat) (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList),
 mem2 (S t) di0 cx0 al0 mem0 ad0 da0 =
 match IsNull (cx2 t di0 cx0 al0 mem0 ad0 da0) return Memo with
 | true => mem2 t di0 cx0 al0 mem0 ad0 da0
 | false =>
     MemoWrite (mem2 t di0 cx0 al0 mem0 ad0 da0)
       (BoolList_to_nat (ad2 t di0 cx0 al0 mem0 ad0 da0))
       (da2 t di0 cx0 al0 mem0 ad0 da0)
 end.
auto.
Qed.

Lemma ad2_t :
 forall (t : nat) (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList),
 ad2 (S t) di0 cx0 al0 mem0 ad0 da0 =
 match IsNull (cx2 t di0 cx0 al0 mem0 ad0 da0) return BoolList with
 | true => ad2 t di0 cx0 al0 mem0 ad0 da0
 | false => BoolList_increment (ad2 t di0 cx0 al0 mem0 ad0 da0)
 end.
auto.
Qed.

Lemma da2_t :
 forall (t : nat) (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList),
 da2 (S t) di0 cx0 al0 mem0 ad0 da0 =
 match IsNull (cx2 t di0 cx0 al0 mem0 ad0 da0) return BoolList with
 | true => da2 t di0 cx0 al0 mem0 ad0 da0
 | false => da2 t di0 cx0 al0 mem0 ad0 da0
 end.
auto.
Qed.

Lemma da2_constant :
 forall (t : nat) (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList),
 da2 t di0 cx0 al0 mem0 ad0 da0 = da0.
simple induction t. simpl in |- *; trivial.
intros. rewrite da2_t. elim (IsNull (cx2 n di0 cx0 al0 mem0 ad0 da0)). apply H.
apply H.
Qed.

(* seq3 *)

Definition di3 (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList) := ad0.
Definition cx3 (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList) := cx0.
Definition al3 (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList) := al0.
Definition mem3 (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList) := mem0.
Definition ad3 (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList) := ad0.
Definition da3 (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList) := da0.

(****************************************************************)

(* seq2.seq1 *)

Definition compo_2_1 (X : Set)
  (f : nat -> BoolList -> BoolList -> BoolList -> Memo -> BoolList -> BoolList -> X)
  (t : nat) (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList) :=
  f t (di1 di0 cx0 al0 mem0 ad0 da0) (cx1 di0 cx0 al0 mem0 ad0 da0)
    (al1 di0 cx0 al0 mem0 ad0 da0) (mem1 di0 cx0 al0 mem0 ad0 da0)
    (ad1 di0 cx0 al0 mem0 ad0 da0) (da1 di0 cx0 al0 mem0 ad0 da0).

Definition di_2_1 := compo_2_1 BoolList di2.
Definition cx_2_1 := compo_2_1 BoolList cx2.
Definition al_2_1 := compo_2_1 BoolList al2.
Definition mem_2_1 := compo_2_1 Memo mem2.
Definition ad_2_1 := compo_2_1 BoolList ad2.
Definition da_2_1 := compo_2_1 BoolList da2.

(* seq3.seq2.seq1 *)

Definition compo' (X : Set) (f : BoolList -> BoolList -> BoolList -> Memo -> BoolList -> BoolList -> X)
  (t : nat) (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList) :=
  f (di_2_1 t di0 cx0 al0 mem0 ad0 da0) (cx_2_1 t di0 cx0 al0 mem0 ad0 da0)
    (al_2_1 t di0 cx0 al0 mem0 ad0 da0) (mem_2_1 t di0 cx0 al0 mem0 ad0 da0)
    (ad_2_1 t di0 cx0 al0 mem0 ad0 da0) (da_2_1 t di0 cx0 al0 mem0 ad0 da0).

Definition di' := compo' BoolList di3.
Definition cx' := compo' BoolList cx3.
Definition al' := compo' BoolList al3.
Definition mem' := compo' Memo mem3.
Definition ad' := compo' BoolList ad3.
Definition da' := compo' BoolList da3.

(****************************************************************)

Lemma cx_cx' :
  forall (a_size d_size: nat)
         (di_init cx_init al_init: BoolList)
         (mem_init: Memo)
         (DC_a DC_d: BoolList)
         (DC_asize: length DC_a = a_size)
         (DC_dsize: length DC_d = d_size)
         (t : nat),
 cx t di_init cx_init al_init mem_init =
 cx' t di_init cx_init al_init mem_init DC_a DC_d.
unfold cx' in |- *. unfold compo' in |- *. unfold cx3 in |- *. unfold cx_2_1, compo_2_1 in |- *.
unfold di1, cx1, al1, mem1, ad1, da1 in |- *. simple induction t. auto.
intros. rewrite cx_t. rewrite cx2_t. rewrite H. trivial.
Qed.

Lemma di_di' :
  forall (a_size d_size: nat)
         (di_init cx_init al_init: BoolList)
         (mem_init: Memo)
         (DC_a DC_d: BoolList)
         (DC_asize: length DC_a = a_size)
         (DC_dsize: length DC_d = d_size)
         (t : nat),
 di t di_init cx_init al_init mem_init =
 di' t di_init cx_init al_init mem_init DC_a DC_d.
unfold di' in |- *. unfold compo' in |- *.
unfold di3 in |- *. unfold ad_2_1, compo_2_1 in |- *. unfold di1, cx1, al1, mem1, ad1, da1 in |- *.
simple induction t. auto.
intros. rewrite di_t. rewrite ad2_t. rewrite H.
replace (cx n di_init cx_init al_init mem_init) with
 (cx' n di_init cx_init al_init mem_init DC_a DC_d).
unfold cx', compo' in |- *. unfold cx3 in |- *. unfold cx_2_1, compo_2_1 in |- *.
unfold di1, cx1, al1, mem1, ad1, da1 in |- *.
trivial. rewrite (cx_cx' a_size d_size di_init cx_init al_init mem_init DC_a DC_d). trivial.
trivial. trivial.

Qed.


Lemma al_al' :
  forall (a_size d_size: nat)
         (di_init cx_init al_init: BoolList)
         (mem_init: Memo)
         (DC_a DC_d: BoolList)
         (DC_asize: length DC_a = a_size)
         (DC_dsize: length DC_d = d_size)
         (t : nat),
 al t di_init cx_init al_init mem_init =
 al' t di_init cx_init al_init mem_init DC_a DC_d.
intros.
rewrite al_constant.
unfold al' in |- *.
unfold compo' in |- *.
unfold al3 in |- *.
unfold al_2_1 in |- *.
unfold compo_2_1 in |- *.
rewrite al2_constant.
unfold al1 in |- *.
trivial.
Qed.

Lemma mem_mem' :
  forall (a_size d_size: nat)
         (di_init cx_init al_init: BoolList)
         (mem_init: Memo)
         (DC_a DC_d: BoolList)
         (DC_asize: length DC_a = a_size)
         (DC_dsize: length DC_d = d_size)
         (t : nat),
 mem t di_init cx_init al_init mem_init =
 mem' t di_init cx_init al_init mem_init DC_a DC_d.
unfold mem', compo' in |- *.
unfold mem3 in |- *.
unfold mem_2_1, compo_2_1 in |- *.
unfold di1, cx1, al1, mem1, ad1, da1 in |- *.
simple induction t.
auto.

intros.
rewrite mem2_t.
rewrite mem_t.
rewrite H.
replace (al n di_init cx_init al_init mem_init) with al_init.
replace (da2 n di_init cx_init al_init mem_init di_init al_init) with al_init.
rewrite (di_di' a_size d_size di_init cx_init al_init mem_init DC_a DC_d DC_asize DC_dsize n).
unfold di' in |- *.
unfold compo' in |- *.
unfold di3 in |- *.
unfold ad_2_1, compo_2_1 in |- *.
unfold di1, cx1, al1, mem1, ad1, da1 in |- *.
rewrite (cx_cx' a_size d_size di_init cx_init al_init mem_init DC_a DC_d DC_asize DC_dsize n).
unfold cx', compo', cx3 in |- *.
unfold cx_2_1, compo_2_1 in |- *.
unfold di1, cx1, al1, mem1, ad1, da1 in |- *.
trivial.

rewrite da2_constant.
trivial.

rewrite al_constant.
trivial.
Qed.

Theorem Fill_ok :
  forall (a_size d_size: nat)
         (di_init cx_init al_init: BoolList)
         (mem_init: Memo)
         (DC_a DC_d: BoolList)
         (DC_asize: length DC_a = a_size)
         (DC_dsize: length DC_d = d_size)
         (t : nat),
 di t di_init cx_init al_init mem_init =
 di' t di_init cx_init al_init mem_init DC_a DC_d /\
 cx t di_init cx_init al_init mem_init =
 cx' t di_init cx_init al_init mem_init DC_a DC_d /\
 al t di_init cx_init al_init mem_init =
 al' t di_init cx_init al_init mem_init DC_a DC_d /\
 mem t di_init cx_init al_init mem_init =
 mem' t di_init cx_init al_init mem_init DC_a DC_d.
split. apply (di_di' a_size d_size di_init cx_init al_init mem_init DC_a DC_d DC_asize DC_dsize).
split. apply (cx_cx' a_size d_size di_init cx_init al_init mem_init DC_a DC_d DC_asize DC_dsize).
split. apply (al_al' a_size d_size di_init cx_init al_init mem_init DC_a DC_d DC_asize DC_dsize). apply (mem_mem' a_size d_size di_init cx_init al_init mem_init DC_a DC_d DC_asize DC_dsize).
Qed.

(* MULTIPLIER/Definitions.v *)

Definition Mux (b : bool) (x y : BoolList) :=
  match b with
  | true => x
  | false => y
  end.

Lemma Mux_neg :
 forall (b : bool) (x y : BoolList), Mux (negb b) x y = Mux b y x.
simple induction b; simpl in |- *; trivial.
Qed.

Lemma Mux_eq : forall (b : bool) (x : BoolList), Mux b x x = x.
simple induction b; simpl in |- *; trivial.
Qed.

Lemma MuxMux :
 forall (b1 b2 : bool) (x x' y y' : BoolList),
 Mux b1 (Mux b2 x y) (Mux b2 x' y') =
 Mux b2 (Mux b1 x x') (Mux b1 y y').
simple induction b2; auto.
Qed.

Lemma Mux_cond_true :
 forall (a : bool) (x y : BoolList), x <> y -> Mux a x y = x -> a = true.
unfold not in |- *. simple induction a; auto.
Qed.

Lemma Mux_cond_false :
 forall (a : bool) (x y : BoolList), x <> y -> Mux a x y = y -> a = false.
unfold not in |- *. simple induction a. simpl in |- *. intros. absurd (x = y). auto.
exact H0. auto.
Qed.

Lemma F_Mux :
 forall (a : bool) (x y : BoolList) (F : BoolList -> BoolList),
 F (Mux a x y) = Mux a (F x) (F y).
simple induction a; auto.
Qed.


Definition lowbit (l : BoolList) :=
  match l with
  | nil => false
  | b :: _ => b
  end.

Definition highs (l : BoolList) :=
  match l with
  | nil => nil
  | _ :: v => v
  end.

Lemma lowbit_is_trunc :
 forall v : BoolList, v <> nil -> cons (lowbit v) nil = trunc v 1.
simple induction v. intro. absurd (nil <> nil); unfold not in |- *; auto with arith.
intros. simpl in |- *. rewrite trunc_O. trivial with arith.
Qed.

Lemma lowbit_is_abit :
 forall v : BoolList, v <> nil -> cons (lowbit v) nil = elemlist v 0.
intros. unfold elemlist in |- *.  rewrite strip_O.
apply lowbit_is_trunc. exact H.
Qed.

Lemma highs_is_strip : forall v : BoolList, highs v = strip v 1.
simple induction v. simpl in |- *. auto with arith.
intros. simpl in |- *. rewrite strip_cons_S. rewrite strip_O. trivial with arith.
Qed.

Lemma app_lowbit_highs :
 forall v : BoolList, v <> nil -> app (cons (lowbit v) nil) (highs v) = v.
intros. rewrite lowbit_is_trunc. rewrite highs_is_strip.
rewrite app_trunc_strip. trivial with arith. exact H.
Qed.

Lemma length_highs :
 forall v : BoolList, v <> nil -> length (highs v) = pred (length v).
intros. rewrite highs_is_strip.
rewrite length_strip. apply minus_n_SO.
apply v_not_nil_length. exact H.
Qed.

Lemma length_abit :
 forall (v : BoolList) (i : nat), i < length v -> length (elemlist v i) = 1.
exact (length_elemlist).
Qed.
(****************************************************************)
(* Defintitions des variables et leurs contraintes *)

Parameter size : nat. (* La taille des mots *)
Parameter V1 : BoolList. (* Les deux entrees *)
Parameter V2 : BoolList.

Axiom size_not_O : size <> 0.
Axiom length_V1_size : length V1 = size.
Axiom length_V2_size : length V2 = size.

Lemma le_SO_size : 1 <= size.
       generalize size_not_O. elim size. intro. absurd (0 <> 0); unfold not in |- *; auto with arith.
       intros. apply le_n_S. auto with arith. Qed.

Lemma length_V1 : length V1 <> 0.
	rewrite length_V1_size. apply size_not_O. Qed.
Lemma length_V2 : length V2 <> 0.
	rewrite length_V2_size. apply size_not_O. Qed.
Lemma length_V2_V1 : length V2 = length V1.
	transitivity size; auto with arith. apply length_V2_size. rewrite length_V1_size. auto. Qed.
Lemma V1_not_nil : V1 <> nil.
	apply not_nil. rewrite length_V1_size. apply size_not_O. Qed.
Lemma V2_not_nil : V2 <> nil.
	apply not_nil. rewrite length_V2_size. apply size_not_O. Qed.
Lemma le_SO_length_V1 : 1 <= length V1.
	apply le_SO_length_v. apply length_V1. Qed.

(****************************************************************)
(* Les registres: *)

Fixpoint R1 (st : nat) : BoolList :=
  match st return BoolList with
  | O => V1
  | S t =>
      app (highs (R1 t))
        (Mux (lowbit (R1 t))
           (cons (lowbit (BoolList_full_adder_sum (R2 t) V2 false)) nil)
           (cons (lowbit (R2 t)) nil))
  end

 with R2 (st : nat) : BoolList :=
  match st return BoolList with
  | O => BoolList_null size
  | S t =>
      app
        (highs
           (Mux (lowbit (R1 t)) (BoolList_full_adder_sum (R2 t) V2 false) (R2 t)))
        (Mux (lowbit (R1 t))
           (cons (BoolList_full_adder_carry (R2 t) V2 false) nil)
           (cons false nil))
  end.


Lemma R1_eq1 : R1 0 = V1. auto with arith. Qed.
Lemma R1_eq2 :
 forall t : nat,
 R1 (S t) =
 app (highs (R1 t))
   (Mux (lowbit (R1 t))
      (cons (lowbit (BoolList_full_adder_sum (R2 t) V2 false)) nil)
      (cons (lowbit (R2 t)) nil)).
auto with arith. Qed.

Lemma R2_eq1 : R2 0 = BoolList_null size. auto with arith. Qed.
Lemma R2_eq2 :
 forall t : nat,
 R2 (S t) =
 app
   (highs (Mux (lowbit (R1 t)) (BoolList_full_adder_sum (R2 t) V2 false) (R2 t)))
   (Mux (lowbit (R1 t)) (cons (BoolList_full_adder_carry (R2 t) V2 false) nil)
      (cons false nil)).
auto with arith. Qed.

(****************************************************************)
Lemma length_R1 : forall t : nat, t <= size -> length (R1 t) = size.
simple induction t. intros. simpl. apply length_V1_size.
intros. rewrite R1_eq2. rewrite length_app.
unfold Mux in |- *. rewrite F_Mux. rewrite (F_Mux BoolList nat _ _ _ (@length bool)). simpl in |- *. rewrite If_eq.
rewrite highs_is_strip. rewrite (length_strip bool). unfold length in H.
rewrite H. symmetry  in |- *. rewrite plus_comm. apply le_plus_minus. auto with arith.
apply le_Sn_le; auto with arith.
unfold length in H. rewrite H. auto with arith.
apply le_Sn_le. exact H0.
Qed. Hint Resolve length_R1.

Lemma length_R2 : forall t : nat, t <= size -> length (R2 t) = size.
simple induction t. simpl in |- *.
unfold length, BoolList_null in |- *. rewrite (length_list_const bool). trivial with arith.
unfold length in |- *. intros. rewrite R2_eq2.
rewrite (length_app bool). unfold Mux, cons.
rewrite (F_If BoolList BoolList _ _ _ highs).
rewrite (F_If BoolList nat _ _ _ (@length bool)).
rewrite highs_is_strip. rewrite (length_strip bool).
rewrite length_BoolList_full_adder_sum. unfold length in |- *.
rewrite H. rewrite highs_is_strip. rewrite (length_strip bool).
rewrite H. rewrite If_eq. rewrite (F_If BoolList nat _ _ _ (@length bool)). simpl in |- *.
rewrite If_eq. symmetry  in |- *. rewrite plus_comm. apply le_plus_minus. auto with arith.
auto with arith. rewrite H. auto with arith.
apply le_Sn_le; exact H0. apply le_Sn_le; exact H0.
unfold length in |- *. rewrite H. auto with arith. apply le_Sn_le; exact H0.
rewrite length_BoolList_full_adder_sum.
unfold length in |- *. rewrite H. auto with arith. apply le_Sn_le; exact H0.
unfold length in |- *. rewrite H. auto with arith. apply le_Sn_le; exact H0.
Qed. Hint Resolve length_R2.

Lemma R1_never_nil : forall t : nat, t <= size -> R1 t <> nil.
intros. apply (not_nil bool). rewrite length_R1. auto with arith. exact H.
Qed.
