(* From coq-projects/circuits/ *)
Require Import Bool.
Require Import Arith.

Definition half_adder_sum (a b : bool) := xorb a b.
Definition half_adder_carry (a b : bool) := a && b.


Definition bool_to_nat (b : bool) :=
  match b with
  | true => 1
  | false => 0
  end.

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
auto.
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

Lemma app_eq2 : forall (x : bool) (l l' : BoolList), (x :: l) ++ l' = x :: l ++ l'.
auto. Qed.


Lemma length_eq2 :
 forall (x : bool) (l : BoolList), length (x :: l) = S (length l).
  auto with arith. Qed.


Definition BV := BoolList.
Definition nilbv : BV := nil.
Definition consbv : bool -> BV -> BV := cons.
Definition appbv : BV -> BV -> BV := app.
Definition lengthbv : BV -> nat := length.

Definition BV_full_adder_sum :=
  (fix F (l : BoolList) : BoolList -> bool -> BV :=
     match l with
     | nil =>
         (fix F0 (l0 : BoolList) : bool -> BV :=
            match l0 with
            | nil => fun _ : bool => nilbv
            | cons b l1 =>
                fun z : bool =>
                consbv (half_adder_sum b z) (F0 l1 (half_adder_carry b z))
            end)
     | cons b l0 =>
         fun x2 : BoolList =>
         match x2 with
         | nil =>
             fun y z : bool =>
             consbv (half_adder_sum y z) (F l0 nil (half_adder_carry y z))
         | cons b0 l1 =>
             fun y z : bool =>
             consbv (full_adder_sum y b0 z)
               (F l0 l1 (full_adder_carry y b0 z))
         end b
     end).


Lemma BV_full_adder_sum_eq1 :
 forall b : bool, BV_full_adder_sum nil nil b = nilbv.
Proof.
 auto.
Qed.

Lemma BV_full_adder_sum_eq2 :
 forall (vh : bool) (vt : BoolList) (b : bool),
 BV_full_adder_sum nil (vh :: vt) b =
 consbv (half_adder_sum vh b)
   (BV_full_adder_sum nil vt (half_adder_carry vh b)).
Proof.
 auto.
Qed.

Lemma BV_full_adder_sum_eq3 :
 forall (vh : bool) (vt : BoolList) (b : bool),
 BV_full_adder_sum (vh :: vt) nil b =
 consbv (half_adder_sum vh b)
   (BV_full_adder_sum vt nil (half_adder_carry vh b)).
Proof.
 auto.
Qed.

Lemma BV_full_adder_sum_eq4 :
 forall (vh : bool) (vt : BoolList) (wh : bool) (wt : BoolList) (b : bool),
 BV_full_adder_sum (vh :: vt) (wh :: wt) b =
 consbv (full_adder_sum vh wh b)
   (BV_full_adder_sum vt wt (full_adder_carry vh wh b)).
Proof.
 auto.
Qed.


Definition BV_full_adder_carry :=
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


Lemma BV_full_adder_carry_eq1 :
 forall b : bool, BV_full_adder_carry nil nil b = b.

Proof.
 auto.
Qed.

Lemma BV_full_adder_carry_eq2 :
 forall (vh : bool) (vt : BoolList) (b : bool),
 BV_full_adder_carry nil (vh :: vt) b =
 BV_full_adder_carry nil vt (half_adder_carry vh b).
Proof.
 auto.
Qed.


Lemma BV_full_adder_carry_eq3 :
 forall (vh : bool) (vt : BoolList) (b : bool),
 BV_full_adder_carry (vh :: vt) nil b =
 BV_full_adder_carry vt nil (half_adder_carry vh b).

Proof.
 auto.
Qed.

Lemma BV_full_adder_carry_eq4 :
 forall (vh : bool) (vt : BoolList) (wh : bool) (wt : BoolList) (b : bool),
 BV_full_adder_carry (vh :: vt) (wh :: wt) b =
 BV_full_adder_carry vt wt (full_adder_carry vh wh b).

Proof.
 auto.
Qed.


Definition BV_full_adder (v w : BV) (cin : bool) : BV :=
  appbv (BV_full_adder_sum v w cin)
    (consbv (BV_full_adder_carry v w cin) nilbv).

(****************************************************************)

Lemma BV_full_adder_sum_v_nil_false :
 forall v : BV, BV_full_adder_sum v nilbv false = v.
unfold nilbv in |- *. simple induction v. trivial. intros.
rewrite BV_full_adder_sum_eq3. rewrite half_adder_carry_false.
rewrite half_adder_sum_false. rewrite H; auto.
Qed.

Lemma BV_full_adder_carry_v_nil_false :
 forall v : BV, BV_full_adder_carry v nilbv false = false.
unfold nilbv in |- *.
simple induction v. trivial. intros.
rewrite BV_full_adder_carry_eq3. rewrite half_adder_carry_false.
trivial.
Qed.

Lemma BV_full_adder_sum_sym :
 forall (v w : BV) (cin : bool),
 BV_full_adder_sum v w cin = BV_full_adder_sum w v cin.
simple induction v. simple induction w. auto. intros.
rewrite BV_full_adder_sum_eq2. rewrite BV_full_adder_sum_eq3.
rewrite H. auto. simple induction w. intro.
rewrite BV_full_adder_sum_eq2. rewrite BV_full_adder_sum_eq3. rewrite H.
auto. intros. repeat rewrite BV_full_adder_sum_eq4. rewrite H.
do 2 rewrite full_adder_carry_sym1. do 2 rewrite full_adder_sum_sym1. auto.
Qed.

Lemma length_BV_full_adder_sum :
 forall (v w : BV) (cin : bool),
 lengthbv v = lengthbv w -> lengthbv (BV_full_adder_sum v w cin) = lengthbv v.
unfold lengthbv in |- *. simple induction v. simple induction w. intros. case cin. simpl in |- *. trivial.
simpl in |- *. trivial.
intros. absurd (length (nil:BoolList) = length (b :: b0)).
simpl in |- *. discriminate. exact H0. simple induction w. simpl in |- *. intros. discriminate H0.
intros. simpl in |- *. rewrite H. trivial. generalize H1. simpl in |- *. auto.
Qed.

Lemma BV_full_adder_carry_sym :
 forall (v w : BV) (cin : bool),
 BV_full_adder_carry v w cin = BV_full_adder_carry w v cin.
simple induction v. simple induction w. auto. intros.
rewrite BV_full_adder_carry_eq2. rewrite BV_full_adder_carry_eq3.
rewrite H; auto. simple induction w. intros. rewrite BV_full_adder_carry_eq2.
rewrite BV_full_adder_carry_eq3.
rewrite H. auto. intros. do 2 rewrite BV_full_adder_carry_eq4.
rewrite H. rewrite full_adder_carry_sym1. auto.
Qed.

Lemma BV_full_adder_sym :
 forall (v w : BV) (cin : bool),
 BV_full_adder v w cin = BV_full_adder w v cin.
unfold BV_full_adder in |- *.
intros.
rewrite BV_full_adder_sum_sym. rewrite BV_full_adder_carry_sym. auto.
Qed.

Fixpoint BV_to_nat (v : BV) : nat :=
  match v return nat with
  | nil => 0
  | cons b w => bool_to_nat b + (BV_to_nat w + BV_to_nat w)
  end.

Fixpoint power2 (n : nat) : nat :=
  match n with
  | O => 1
  | S x => power2 x + power2 x
  end.

Lemma BV_to_nat_app :
 forall (l n : BV) (ll : nat),
 (******************)
 length l = ll -> BV_to_nat (appbv l n) = BV_to_nat l + power2 ll * BV_to_nat n.
unfold BV, appbv in |- *. simple induction l. intros. inversion H. simpl in |- *. auto.
intros. simpl.
destruct ll.
inversion H0.
inversion H0.
rewrite (H n ll H2).
rewrite <- (plus_assoc (bool_to_nat b) (BV_to_nat b0 + BV_to_nat b0)).
f_equal.
rewrite <- plus_assoc.
rewrite <- (plus_assoc (BV_to_nat b0) (BV_to_nat b0)).
f_equal.
simpl.

rewrite mult_plus_distr_r. repeat rewrite plus_assoc.
subst.
rewrite <- plus_assoc.
rewrite Nat.add_comm.
reflexivity.
Qed.

Lemma BV_to_nat_app2 :
 forall l n : BV,
 (*******************)
 BV_to_nat (appbv l n) = BV_to_nat l + power2 (lengthbv l) * BV_to_nat n.
intros. apply BV_to_nat_app. auto.
Qed.

Lemma BV_full_adder_nil_true_ok :
 forall v : BV, BV_to_nat (BV_full_adder v nilbv true) = S (BV_to_nat v).
unfold nilbv in |- *. simple induction v; auto with arith. unfold BV_full_adder in |- *. intros.
rewrite BV_full_adder_sum_eq3. rewrite BV_full_adder_carry_eq3. unfold appbv.
rewrite app_eq2. rewrite half_adder_carry_true.
simpl in |- *. elim b. unfold appbv in H. rewrite H. simpl in |- *. auto with arith.
rewrite BV_full_adder_sum_v_nil_false.
rewrite BV_full_adder_carry_v_nil_false. rewrite BV_to_nat_app2.
simpl in |- *. elim mult_n_O. elim plus_n_O. trivial with arith.
Qed.


Lemma BV_full_adder_nil_ok :
 forall (v : BV) (cin : bool),
 BV_to_nat (BV_full_adder v nilbv cin) = BV_to_nat v + bool_to_nat cin.

simple induction v. simple induction cin; auto with arith.
simple induction cin. rewrite BV_full_adder_nil_true_ok. simpl in |- *. rewrite Nat.add_1_r. reflexivity.
unfold BV_full_adder in |- *. rewrite BV_full_adder_sum_v_nil_false.
rewrite BV_full_adder_carry_v_nil_false. rewrite BV_to_nat_app2.
simpl in |- *. elim mult_n_O. elim plus_n_O. trivial with arith.
Qed.

(****************************************************************)

Require Import Lia.
Theorem BV_full_adder_ok :
 forall (v w : BV) (cin : bool),
 BV_to_nat (BV_full_adder v w cin) =
 BV_to_nat v + BV_to_nat w + bool_to_nat cin.
simple induction v.
intros.
rewrite BV_full_adder_sym.
simpl in |- *.
rewrite BV_full_adder_nil_ok.
auto with arith.

unfold BV_full_adder in |- *.
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
 (BV_to_nat l + bool_to_nat (half_adder_carry a cin) +
  (BV_to_nat l + bool_to_nat (half_adder_carry a cin))) with
 (bool_to_nat (half_adder_carry a cin) + bool_to_nat (half_adder_carry a cin) +
  (BV_to_nat l + BV_to_nat l)).
repeat rewrite plus_assoc.
replace
 (bool_to_nat (half_adder_sum a cin) + bool_to_nat (half_adder_carry a cin) +
  bool_to_nat (half_adder_carry a cin)) with
 (bool_to_nat (half_adder_sum a cin) +
  (bool_to_nat (half_adder_carry a cin) +
   bool_to_nat (half_adder_carry a cin))).
rewrite half_adder_ok.
rewrite (plus_permute2 (bool_to_nat a) (bool_to_nat cin) (BV_to_nat l)).
rewrite
 (plus_permute2 (bool_to_nat a + BV_to_nat l) (bool_to_nat cin) (BV_to_nat l))
 .
trivial with arith.

trivial with arith.

repeat rewrite plus_assoc.
rewrite
 (plus_permute2 (bool_to_nat (half_adder_carry a cin))
    (bool_to_nat (half_adder_carry a cin)) (BV_to_nat l))
 .
rewrite (plus_comm (bool_to_nat (half_adder_carry a cin)) (BV_to_nat l)).
rewrite
 (plus_permute2 (BV_to_nat l + bool_to_nat (half_adder_carry a cin))
    (bool_to_nat (half_adder_carry a cin)) (BV_to_nat l))
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
(*  (plus_permute2 (bool_to_nat a0 + BV_to_nat l) (BV_to_nat l0) (BV_to_nat l)) *)
(*  . *)
(* rewrite (plus_comm (bool_to_nat a0) (BV_to_nat l)). *)
(* rewrite (plus_permute2 (BV_to_nat l) (bool_to_nat a0) (BV_to_nat l)). *)
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
rewrite (plus_permute2 (BV_to_nat l) (BV_to_nat l0) (BV_to_nat l)).
trivial with arith.

simpl in |- *.
repeat rewrite <- plus_n_Sm.
repeat rewrite <- plus_n_O.
repeat rewrite plus_assoc.
try trivial with arith.
rewrite (plus_permute2 (BV_to_nat l) (BV_to_nat l0) (BV_to_nat l)).
try trivial with arith.

elim a0.
simpl in |- *.
repeat rewrite <- plus_n_Sm.
repeat rewrite <- plus_n_O.
repeat rewrite plus_assoc.
simpl in |- *.
rewrite (plus_permute2 (BV_to_nat l) (BV_to_nat l0) (BV_to_nat l)).
trivial with arith.

simpl in |- *.
repeat rewrite <- plus_n_O.
repeat rewrite plus_assoc.
rewrite (plus_permute2 (BV_to_nat l) (BV_to_nat l0) (BV_to_nat l)).
trivial with arith.

elim a0; simpl in |- *; repeat rewrite <- plus_n_Sm;
 repeat rewrite <- plus_n_O; repeat rewrite plus_assoc;
 rewrite (plus_permute2 (BV_to_nat l) (BV_to_nat l0) (BV_to_nat l));
 trivial with arith.

Qed.
