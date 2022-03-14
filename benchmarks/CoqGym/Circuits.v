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

Fixpoint length (l: BoolList): nat :=
  match l with
  | nil => O
  | cons _ l' => S (length l')
  end.

Fixpoint app (l m: BoolList): BoolList :=
  match l with
  | nil => m
  | cons a l1 => cons a (app l1 m)
  end.

Infix "++" := app (right associativity, at level 60).

Lemma app_eq2 : forall (x : bool) (l l' : BoolList), (cons x l) ++ l' = cons x (l ++ l').
auto. Qed.


Lemma length_eq2 :
 forall (x : bool) (l : BoolList), length (cons x l) = S (length l).
  auto with arith. Qed.

Fixpoint BV_full_adder_sum_nil (l0: BoolList) (b0: bool): BoolList :=
  match l0 with
  | nil => nil
  | cons b l1 => cons (half_adder_sum b b0)
                      (BV_full_adder_sum_nil l1 (half_adder_carry b b0))
  end.

Fixpoint BV_full_adder_sum (l m: BoolList) (bb: bool): BoolList :=
  match l with
  | nil => BV_full_adder_sum_nil m bb
  | cons b l0 =>
    match m with
    | nil =>
      cons (half_adder_sum b bb) (BV_full_adder_sum l0 nil (half_adder_carry b bb))
    | cons b0 l1 =>
      cons (full_adder_sum b b0 bb)
           (BV_full_adder_sum l0 l1 (full_adder_carry b b0 bb))
    end
  end.


(* Definition BV_full_adder_sum := *)
(*   (fix F (l : BoolList) : BoolList -> bool -> BoolList := *)
(*      match l with *)
(*      | nil => *)
(*          (fix F0 (l0 : BoolList) : bool -> BoolList := *)
(*             match l0 with *)
(*             | nil => fun _ : bool => nil *)
(*             | cons b l1 => *)
(*                 fun z : bool => *)
(*                 cons (half_adder_sum b z) (F0 l1 (half_adder_carry b z)) *)
(*             end) *)
(*      | cons b l0 => *)
(*          fun x2 : BoolList => *)
(*          match x2 with *)
(*          | nil => *)
(*              fun y z : bool => *)
(*              cons (half_adder_sum y z) (F l0 nil (half_adder_carry y z)) *)
(*          | cons b0 l1 => *)
(*              fun y z : bool => *)
(*              cons (full_adder_sum y b0 z) *)
(*                (F l0 l1 (full_adder_carry y b0 z)) *)
(*          end b *)
(*      end). *)


Lemma BV_full_adder_sum_eq1 :
 forall b : bool, BV_full_adder_sum nil nil b = nil.
Proof.
 auto.
Qed.

Lemma BV_full_adder_sum_eq2 :
 forall (vh : bool) (vt : BoolList) (b : bool),
 BV_full_adder_sum nil (cons vh vt) b =
 cons (half_adder_sum vh b)
   (BV_full_adder_sum nil vt (half_adder_carry vh b)).
Proof.
 auto.
Qed.

Lemma BV_full_adder_sum_eq3 :
 forall (vh : bool) (vt : BoolList) (b : bool),
 BV_full_adder_sum (cons vh vt) nil b =
 cons (half_adder_sum vh b)
   (BV_full_adder_sum vt nil (half_adder_carry vh b)).
Proof.
 auto.
Qed.

Lemma BV_full_adder_sum_eq4 :
 forall (vh : bool) (vt : BoolList) (wh : bool) (wt : BoolList) (b : bool),
 BV_full_adder_sum (cons vh vt) (cons wh wt) b =
 cons (full_adder_sum vh wh b)
   (BV_full_adder_sum vt wt (full_adder_carry vh wh b)).
Proof.
 auto.
Qed.

Fixpoint BV_full_adder_carry_nil (l0: BoolList) (bb: bool): bool :=
  match l0 with
  | nil => bb
  | cons b l1 => BV_full_adder_carry_nil l1 (half_adder_carry b bb)
  end.

Fixpoint BV_full_adder_carry (l m: BoolList) (bb: bool) :=
  match l with
  | nil => BV_full_adder_carry_nil m bb
  | cons b l0 =>
    match m with
    | nil => BV_full_adder_carry l0 nil (half_adder_carry b bb)
    | cons b0 l1 => BV_full_adder_carry l0 l1 (full_adder_carry b b0 bb)
    end
  end.


(* Definition BV_full_adder_carry :=
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
     end). *)


Lemma BV_full_adder_carry_eq1 :
 forall b : bool, BV_full_adder_carry nil nil b = b.

Proof.
 auto.
Qed.

Lemma BV_full_adder_carry_eq2 :
 forall (vh : bool) (vt : BoolList) (b : bool),
 BV_full_adder_carry nil (cons vh vt) b =
 BV_full_adder_carry nil vt (half_adder_carry vh b).
Proof.
 auto.
Qed.


Lemma BV_full_adder_carry_eq3 :
 forall (vh : bool) (vt : BoolList) (b : bool),
 BV_full_adder_carry (cons vh vt) nil b =
 BV_full_adder_carry vt nil (half_adder_carry vh b).

Proof.
 auto.
Qed.

Lemma BV_full_adder_carry_eq4 :
 forall (vh : bool) (vt : BoolList) (wh : bool) (wt : BoolList) (b : bool),
 BV_full_adder_carry (cons vh vt) (cons wh wt) b =
 BV_full_adder_carry vt wt (full_adder_carry vh wh b).

Proof.
 auto.
Qed.


Definition BV_full_adder (v w : BoolList) (cin : bool) : BoolList :=
  app (BV_full_adder_sum v w cin)
    (cons (BV_full_adder_carry v w cin) nil).

(****************************************************************)

Lemma BV_full_adder_sum_v_nil_false :
 forall v : BoolList, BV_full_adder_sum v nil false = v.
simple induction v. trivial. intros.
rewrite BV_full_adder_sum_eq3. rewrite half_adder_carry_false.
rewrite half_adder_sum_false. rewrite H; auto.
Qed.

Lemma BV_full_adder_carry_v_nil_false :
 forall v : BoolList, BV_full_adder_carry v nil false = false.
simple induction v. trivial. intros.
rewrite BV_full_adder_carry_eq3. rewrite half_adder_carry_false.
trivial.
Qed.

Lemma BV_full_adder_sum_sym :
 forall (v w : BoolList) (cin : bool),
 BV_full_adder_sum v w cin = BV_full_adder_sum w v cin.
simple induction v. simple induction w. auto. intros.
rewrite BV_full_adder_sum_eq2. rewrite BV_full_adder_sum_eq3.
rewrite H. auto. simple induction w. intro.
rewrite BV_full_adder_sum_eq2. rewrite BV_full_adder_sum_eq3. rewrite H.
auto. intros. repeat rewrite BV_full_adder_sum_eq4. rewrite H.
do 2 rewrite full_adder_carry_sym1. do 2 rewrite full_adder_sum_sym1. auto.
Qed.

Lemma length_BV_full_adder_sum :
 forall (v w : BoolList) (cin : bool),
 length v = length w -> length (BV_full_adder_sum v w cin) = length v.
unfold length in |- *. simple induction v. simple induction w. intros. case cin. simpl in |- *. trivial.
simpl in |- *. trivial.
intros. absurd (length (nil:BoolList) = length (cons b b0)).
simpl in |- *. discriminate. exact H0. simple induction w. simpl in |- *. intros. discriminate H0.
intros. simpl in |- *. rewrite H. trivial. generalize H1. simpl in |- *. auto.
Qed.

Lemma BV_full_adder_carry_sym :
 forall (v w : BoolList) (cin : bool),
 BV_full_adder_carry v w cin = BV_full_adder_carry w v cin.
simple induction v. simple induction w. auto. intros.
rewrite BV_full_adder_carry_eq2. rewrite BV_full_adder_carry_eq3.
rewrite H; auto. simple induction w. intros. rewrite BV_full_adder_carry_eq2.
rewrite BV_full_adder_carry_eq3.
rewrite H. auto. intros. do 2 rewrite BV_full_adder_carry_eq4.
rewrite H. rewrite full_adder_carry_sym1. auto.
Qed.

Lemma BV_full_adder_sym :
 forall (v w : BoolList) (cin : bool),
 BV_full_adder v w cin = BV_full_adder w v cin.
unfold BV_full_adder in |- *.
intros.
rewrite BV_full_adder_sum_sym. rewrite BV_full_adder_carry_sym. auto.
Qed.

Fixpoint BV_to_nat (v : BoolList) : nat :=
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
 forall (l n : BoolList) (ll : nat),
 (******************)
 length l = ll -> BV_to_nat (app l n) = BV_to_nat l + power2 ll * BV_to_nat n.
simple induction l. intros. inversion H. simpl in |- *. auto.
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
 forall l n : BoolList,
 (*******************)
 BV_to_nat (app l n) = BV_to_nat l + power2 (length l) * BV_to_nat n.
intros. apply BV_to_nat_app. auto.
Qed.

Lemma BV_full_adder_nil_true_ok :
 forall v : BoolList, BV_to_nat (BV_full_adder v nil true) = S (BV_to_nat v).
simple induction v; auto with arith. unfold BV_full_adder in |- *. intros.
rewrite BV_full_adder_sum_eq3. rewrite BV_full_adder_carry_eq3.
rewrite app_eq2. rewrite half_adder_carry_true.
simpl in |- *. elim b. rewrite H. simpl in |- *. auto with arith.
rewrite BV_full_adder_sum_v_nil_false.
rewrite BV_full_adder_carry_v_nil_false. rewrite BV_to_nat_app2.
simpl in |- *. elim mult_n_O. elim plus_n_O. trivial with arith.
Qed.


Lemma BV_full_adder_nil_ok :
 forall (v : BoolList) (cin : bool),
 BV_to_nat (BV_full_adder v nil cin) = BV_to_nat v + bool_to_nat cin.

simple induction v. simple induction cin; auto with arith.
simple induction cin. rewrite BV_full_adder_nil_true_ok. simpl in |- *. rewrite Nat.add_1_r. reflexivity.
unfold BV_full_adder in |- *. rewrite BV_full_adder_sum_v_nil_false.
rewrite BV_full_adder_carry_v_nil_false. rewrite BV_to_nat_app2.
simpl in |- *. elim mult_n_O. elim plus_n_O. trivial with arith.
Qed.

(****************************************************************)

Require Import Lia.
Theorem BV_full_adder_ok :
 forall (v w : BoolList) (cin : bool),
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


(*********************************************************)

Parameter size : nat. (* La taille des mots *)
Parameter V1 : BoolList. (* Les deux entrees *)
Parameter V2 : BoolList.

Axiom size_not_O : size <> 0. Hint Resolve size_not_O.
Axiom length_V1_size : length V1 = size. Hint Resolve length_V1_size.
Axiom length_V2_size : length V2 = size. Hint Resolve length_V2_size.

Definition Mux (b : bool) (x y: BoolList) :=
  match b with
  | true => x
  | false => y
  end.

Definition lowbit (l : BoolList) :=
  match l with
  | nil => false
  | cons b _ => b
  end.

Definition highs (l : BoolList) :=
  match l with
  | nil => nil
  | cons _ v => v
  end.

Fixpoint BV_null (n: nat) : BoolList :=
  match n with
  | O => nil
  | S n => cons false (BV_null n)
  end.

Fixpoint R1 (st : nat) : BoolList :=
  match st return BoolList with
  | O => V1
  | S t =>
      app (highs (R1 t))
        (Mux (lowbit (R1 t))
           (cons (lowbit (BV_full_adder_sum (R2 t) V2 false)) nil)
           (cons (lowbit (R2 t)) nil))
  end

 with R2 (st : nat) : BoolList:=
  match st return BoolList with
  | O => BV_null size
  | S t =>
      app
        (highs
           (Mux (lowbit (R1 t)) (BV_full_adder_sum (R2 t) V2 false) (R2 t)))
        (Mux (lowbit (R1 t))
           (cons (BV_full_adder_carry (R2 t) V2 false) nil)
           (cons false nil))
  end.

Lemma R1_eq1 : R1 0 = V1. auto with arith. Qed.
Lemma R1_eq2 :
 forall t : nat,
 R1 (S t) =
 app (highs (R1 t))
   (Mux (lowbit (R1 t))
      (cons (lowbit (BV_full_adder_sum (R2 t) V2 false)) nil)
      (cons (lowbit (R2 t)) nil)).
auto with arith. Qed.

Lemma R2_eq1 : R2 0 = BV_null size. auto with arith. Qed.
Lemma R2_eq2 :
 forall t : nat,
 R2 (S t) =
 app
   (highs (Mux (lowbit (R1 t)) (BV_full_adder_sum (R2 t) V2 false) (R2 t)))
   (Mux (lowbit (R1 t)) (cons (BV_full_adder_carry (R2 t) V2 false) nil)
      (cons false nil)).
auto with arith. Qed.

(****************************************************************)
Fixpoint rev (v : BoolList) : BoolList :=
  match v with
  | nil => nil
  | cons head tail => app (rev tail) (cons head nil)
  end.

Fixpoint trunc (v : BoolList) : nat -> BoolList :=
  fun n : nat =>
  match v return (BoolList) with
  | nil => nil
  | cons b w =>
      match n return (BoolList) with
      | O => nil
      | S p => cons b (trunc w p)
      end
  end.

Definition strip (v : BoolList) (n : nat) :=
  rev (trunc (rev v) (length v - n)).


Lemma length_app :
 forall v1 v2 : BoolList,
 (***************)
 length (v1 ++ v2) = length v1 + length v2.
simple induction v1. simpl in |- *. trivial with arith.
intros. simpl in |- *. rewrite H. trivial with arith.
Qed.

Lemma plus_n_SO : forall x : nat, x + 1 = S x.
intros; rewrite plus_comm; auto with arith.
Qed.

Lemma length_rev : forall l : BoolList, length (rev l) = length l.
(***************)
simple induction l; auto with arith. intros. simpl in |- *.
rewrite length_app. simpl in |- *. rewrite plus_n_SO. rewrite H. trivial with arith.
Qed.

Lemma trunc_all : forall v : BoolList, trunc v (length v) = v.
(**************)
simple induction v. simpl in |- *. trivial with arith.
intros. rewrite length_eq2. simpl in |- *. rewrite H. trivial with arith.
Qed.

Lemma cons_assoc_app : forall (b : bool) (v1 v2: BoolList),
    cons b (v1 ++ v2) = (cons b v1) ++ v2.
  induction v1; induction v2; auto.
Qed.

Lemma app_v_nil : forall v : BoolList, v ++ nil = v.
  (**************)
  induction v.
  simpl. reflexivity.
  rewrite <- cons_assoc_app.
  rewrite IHv.
  reflexivity.
Qed.

Lemma app_assoc_r : forall v1 v2 v3: BoolList, (v1 ++ v2) ++ v3 = v1 ++ (v2 ++ v3).
Proof.
  induction v1; induction v2; induction v3; repeat rewrite app_v_nil; auto.
  simpl. f_equal. rewrite IHv1. simpl. reflexivity.
Qed.

Lemma rev_app : forall l n : BoolList, rev (l ++ n) = rev n ++ rev l.
(************)
  simple induction l; auto with arith.
  { simpl. intro. rewrite app_v_nil. reflexivity. }
  { intros. simpl in |- *. rewrite H. apply app_assoc_r. }
Qed.

Lemma rev_rev : forall l : BoolList, rev (rev l) = l.
(************)
simple induction l; auto with arith. intros; simpl in |- *. rewrite rev_app. rewrite H. auto with arith.
Qed.

Lemma strip_O : forall v : BoolList, strip v 0 = v.
(************)
intro. unfold strip in |- *. rewrite <- minus_n_O. rewrite <- length_rev.
rewrite trunc_all. rewrite rev_rev. trivial with arith.
Qed.

Lemma trunc_O : forall v : BoolList, trunc v 0 = nil.
(************)
simple induction v; auto with arith.
Qed.

Lemma strip_all : forall v : BoolList, strip v (length v) = nil.
(**************)
unfold strip in |- *. intro. rewrite <- minus_n_n. rewrite trunc_O. auto with arith.
Qed.

Lemma BV_null_nat : forall n : nat, BV_to_nat (BV_null n) = 0.
(****************)
unfold BV_null in |- *.
simple induction n; auto.
intros. simpl in |- *. rewrite H. auto.
Qed.

Lemma lowbit_is_trunc :
 forall v : BoolList, v <> nil -> cons (lowbit v) nil = trunc v 1.
simple induction v. intro. absurd (nil <> nil); unfold not in |- *; auto with arith.
intros. simpl in |- *. rewrite trunc_O. trivial with arith.
Qed.


Lemma Invariant_t_O :
 BV_to_nat (app (strip (R1 0) size) (R2 0)) =
 BV_to_nat V2 * BV_to_nat (trunc V1 0).
intros. simpl in |- *.
rewrite BV_to_nat_app2. rewrite trunc_O. rewrite <- length_V1_size.
rewrite strip_all. rewrite length_V1_size.
simpl in |- *. elim plus_n_O. elim mult_n_O. rewrite BV_null_nat. trivial with arith.
Qed.

(****************************************************************)
(* Ensuite, lors de la preuve par induction pour t quelconque,
   on doit faire une preuve par cas selon R1[0].
   On fait la preuve pour R1[0]=false:  (assez long)
 *)

Definition abit (v : BoolList) (i : nat) := trunc (strip v i) 1.

Lemma lowbit_is_abit :
 forall v : BoolList, v <> nil -> cons (lowbit v) nil = abit v 0.
intros. unfold abit in |- *. rewrite strip_O.
apply lowbit_is_trunc. exact H.
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

Lemma rev_eq : forall l n : BoolList, l = n -> rev l = rev n.
(***********)
intros; replace l with n; auto with arith.
Qed.


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

Lemma strip_cons_S :
 forall (v : BoolList) (i : nat) (b : bool),
 (*****************)
 strip (cons b v) (S i) = strip v i.
unfold strip in |- *. simple induction i. simpl in |- *.
elim minus_n_O. intro. replace (length v) with (length (rev v)).
rewrite trunc_all. rewrite trunc_app. rewrite trunc_all.
elim minus_n_n. rewrite trunc_O. rewrite app_v_nil. trivial with arith.
apply length_rev.
intros. apply rev_eq. simpl in |- *.
rewrite trunc_app. rewrite length_rev. rewrite minus_minus_lem1.
rewrite trunc_O. rewrite app_v_nil. trivial with arith.
Qed.
Lemma highs_is_strip : forall v : BoolList, highs v = strip v 1.
simple induction v. simpl in |- *. auto with arith.
intros. simpl in |- *. rewrite strip_cons_S. rewrite strip_O. trivial with arith.
Qed.


Lemma length_trunc :
 forall (v : BoolList) (i : nat),
 (*****************)
 i <= length v -> length (trunc v i) = i.
simple induction v. simpl in |- *. auto with arith.
intros b b0 H. simple induction i. simpl in |- *. trivial with arith.
simpl in |- *. intros. apply eq_S. apply H. apply le_S_n. exact H1.
Qed.


Lemma length_strip :
 forall (v : BoolList) (i : nat),
 (*****************)
 i <= length v -> length (strip v i) = length v - i.
unfold strip in |- *. intros. rewrite length_rev. rewrite length_trunc. trivial with arith.
rewrite length_rev. apply minus_le_lem2.
Qed.

Lemma length_if: forall (b: bool) (v1 v2: BoolList),
    length (if b then v1 else v2) = if b then length v1 else length v2.
Proof.
  simple induction b; auto.
Qed.

Lemma highs_if: forall (b: bool) (v1 v2: BoolList),
    highs (if b then v1 else v2) = if b then highs v1 else highs v2.
Proof.
  simple induction b; auto.
Qed.

Lemma If_eq_nat: forall (b: bool) (n: nat),
    (if b then n else n) = n.
Proof.
  simple induction b; auto.
Qed.

Lemma length_R1 : forall t : nat, t <= size -> length (R1 t) = size.
simple induction t. auto with arith.
intros. rewrite R1_eq2. rewrite length_app.
unfold Mux in |- *. rewrite length_if. simpl in |- *. rewrite If_eq_nat.
rewrite highs_is_strip. rewrite length_strip. (* unfold length in H.*)
rewrite H. symmetry  in |- *. rewrite plus_comm. lia.
apply le_Sn_le; auto with arith. rewrite H. lia. lia.
Qed.


Fixpoint list_const (n : nat) : bool -> BoolList :=

 (*****************)
 fun x : bool =>
 match n return BoolList with
 | O => nil
 | S n' => cons x (list_const n' x)
 end.

Lemma length_list_const :
 forall (n : nat) (x : bool), length (BV_null n) = n.
(**********************)
simple induction n. auto with arith. intros. simpl in |- *. auto with arith.
Qed.

Lemma length_R2 : forall t : nat, t <= size -> length (R2 t) = size.
  simple induction t. simpl in |- *.
rewrite length_list_const. trivial with arith. exact true.
intros. rewrite R2_eq2.
rewrite length_app. unfold Mux.
rewrite highs_if.
rewrite length_if.
rewrite highs_is_strip. rewrite length_strip.
rewrite length_BV_full_adder_sum.
rewrite H. rewrite highs_is_strip. rewrite length_strip.
rewrite H. rewrite If_eq_nat. rewrite length_if. simpl in |- *.
rewrite If_eq_nat. symmetry  in |- *. rewrite plus_comm. apply le_plus_minus. lia. lia. lia. lia.  rewrite H. apply eq_sym. apply length_V2_size. lia.
rewrite length_BV_full_adder_sum.
rewrite H. lia. apply le_Sn_le; exact H0.
rewrite H. apply eq_sym. apply length_V2_size. lia.
Qed.

Lemma not_nil : forall v : BoolList, length v <> 0 -> v <> nil.
(************)
simple induction v. simpl in |- *; intro. absurd (0 <> 0). unfold not in |- *; auto with arith. exact H.
simpl in |- *. intros. discriminate.
Qed.

Lemma R1_never_nil : forall t : nat, t <= size -> R1 t <> nil.
intros. apply not_nil. rewrite length_R1. auto with arith. exact H.
Qed.

Lemma strip_nil : forall i : nat, strip nil i = nil.
(**************)
intro. auto with arith.
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

Lemma strip_strip :
 forall (v : BoolList) (i j : nat),
 (****************)
 strip (strip v i) j = strip v (i + j).
simple induction v. intros. rewrite strip_nil. rewrite strip_nil. trivial with arith.
simple induction i. intro. simpl in |- *. rewrite strip_O. trivial with arith.
simple induction j. rewrite strip_O. elim plus_n_O. trivial with arith.
intros. rewrite strip_cons_S. simpl in |- *. rewrite strip_cons_S. apply H.
Qed.

Lemma power2_eq2 : forall x : nat, power2 (S x) = power2 x + power2 x.
Proof.
 auto with arith.
Qed.

Lemma mult_sym : forall a b : nat, a * b = b * a.
intros a b; elim a; simpl in |- *; auto with arith.
intros y H.
replace (y * b) with (b * y).
elim (mult_n_Sm b y).
apply plus_comm.
Qed.

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

Lemma app_lowbit_highs :
 forall v : BoolList, v <> nil -> app (cons (lowbit v) nil) (highs v) = v.
intros. rewrite lowbit_is_trunc. rewrite highs_is_strip.
rewrite app_trunc_strip. trivial with arith. exact H.
Qed.

Lemma BV_nat_lem1 :
 forall (v : BoolList) (n : nat),
 length v <> 0 ->
 power2 n * BV_to_nat (cons (lowbit v) nil) +
 power2 (S n) * BV_to_nat (highs v) = power2 n * BV_to_nat v.

intros. rewrite power2_eq2. rewrite mult_plus_distr_r.
replace (BV_to_nat v) with
 (BV_to_nat (app (cons (lowbit v) nil) (highs v))).
rewrite BV_to_nat_app2.
rewrite
 (mult_sym (power2 n)
    (BV_to_nat (cons (lowbit v) nil) +
     power2 (length (cons (lowbit v) nil)) * BV_to_nat (highs v)))
 .
rewrite mult_plus_distr_r.
simpl in |- *. elim plus_n_O. elim plus_n_O. rewrite mult_plus_distr_r.
rewrite (mult_sym (power2 n)). rewrite (mult_sym (power2 n)). trivial with arith.
rewrite app_lowbit_highs. trivial with arith.
apply not_nil. exact H.
Qed.

Lemma le_minus_minus : forall a b c : nat, c <= b -> a - b <= a - c.
simple induction a. simpl in |- *. auto with arith.
intros. generalize H0. elim c. elim minus_n_O. intro. apply minus_le_lem2.
elim b. intros. absurd (S n0 <= 0). auto with arith.
exact H2.
intros. simpl in |- *. apply H. apply le_S_n. exact H3.
Qed.

Lemma v_not_nil_length :
 forall v : BoolList,
 (*********************)
 v <> nil -> 1 <= length v.
simple induction v. intro. absurd (nil <> nil :>BoolList). unfold not in |- *. auto with arith.
exact H.
intros. simpl in |- *. apply le_n_S. auto with arith.
Qed.

Lemma length_highs :
 forall v : BoolList, v <> nil -> length (highs v) = pred (length v).
intros. rewrite highs_is_strip.
rewrite length_strip. apply minus_n_SO.
apply v_not_nil_length. exact H.
Qed.

Lemma inv_ind_false :
 forall t n : nat,
 (n <= size ->
  BV_to_nat (app (strip (R1 n) (size - n)) (R2 n)) =
  BV_to_nat V2 * BV_to_nat (trunc V1 n)) ->
 S n <= size ->
 n <= size ->
 BV_to_nat
   (app
      (strip
         (app (highs (R1 n))
            (Mux false (abit (BV_full_adder_sum (R2 n) V2 false) 0)
               (cons (lowbit (R2 n)) nil))) (size - S n))
      (app (highs (Mux false (BV_full_adder_sum (R2 n) V2 false) (R2 n)))
         (Mux false (cons (BV_full_adder_carry (R2 n) V2 false) nil)
            (cons false nil)))) =
 BV_to_nat V2 * BV_to_nat (app (trunc V1 n) (cons false nil)).
intros.
simpl in |- *.
do 3 rewrite BV_to_nat_app2.
simpl in |- *.
elim mult_n_O.
elim mult_n_O.
elim plus_n_O.
elim plus_n_O.
rewrite length_strip.
rewrite <- H.
clear H.
rewrite length_app.
rewrite highs_is_strip.
rewrite length_strip.
rewrite length_R1.
simpl in |- *.
replace (size - 1 + 1) with size.
rewrite minus_minus_lem2.
rewrite strip_app.
rewrite BV_to_nat_app2.
rewrite strip_strip.
rewrite length_strip.
rewrite length_R1.
rewrite length_strip.
rewrite BV_to_nat_app2.
rewrite length_strip.
rewrite length_R1.
rewrite minus_minus_lem2.
replace (1 + (size - S n)) with (size - n).
rewrite minus_minus_lem2.
rewrite (minus_le_O (size - S n) (size - 1)).
rewrite strip_O.
rewrite plus_assoc_reverse.
replace
 (power2 n * BV_to_nat (cons (lowbit (R2 n)) nil) +
  power2 (S n) * BV_to_nat (highs (R2 n))) with (power2 n * BV_to_nat (R2 n)).
trivial with arith. symmetry  in |- *. apply BV_nat_lem1.
rewrite length_R2. exact size_not_O. exact H1. apply le_minus_minus; auto with arith.
exact H1. simpl in |- *. rewrite minus_Sn_m. auto with arith.
exact H0. exact H1. exact H1. rewrite length_R1. lia. exact H1.
rewrite length_R1. lia.  exact H1. exact H1. rewrite length_R1.
simpl in |- *. rewrite minus_Sn_m. simpl in |- *. lia. exact H0. exact H1.
exact H0. rewrite plus_comm. simpl in |- *. rewrite minus_Sn_m; lia.
 exact H1. rewrite length_R1. lia. exact H1. exact H1.
rewrite length_app. rewrite length_highs. rewrite length_R1.
simpl in |- *. rewrite plus_n_SO. replace (pred size) with (size - 1).
rewrite minus_Sn_m. simpl in |- *. elim minus_n_O. apply minus_le_lem2; lia. lia. lia. lia.
apply not_nil. rewrite length_R1. auto. auto.
Qed.

(****************************************************************)
(* Puis pour le cas ou R1[0]=true (tres tres long !!!!!)
*)

Lemma mult_plus_distr2 : forall n m p : nat, n * (m + p) = n * m + n * p.
intros. rewrite mult_sym. rewrite mult_plus_distr_r. rewrite mult_sym.
replace (p * n) with (n * p). trivial with arith. apply mult_sym.
Qed.


Lemma length_abit :
 forall (v : BoolList) (i : nat), i < length v -> length (abit v i) = 1.
intros. unfold abit in |- *. rewrite length_trunc. trivial with arith.
rewrite length_strip. inversion H. rewrite <- minus_Sn_m. auto with arith. auto with arith.
rewrite <- minus_Sn_m. auto with arith. apply le_Sn_le. exact H1. apply lt_le_weak. exact H.
Qed.

Lemma power2_plus : forall x y : nat, power2 (x + y) = power2 x * power2 y.
simple induction x. intros. simpl in |- *. elim plus_n_O; auto with arith.
intros. simpl in |- *. rewrite H. rewrite mult_plus_distr_r. trivial with arith.
Qed.

Lemma inv_ind_true :
 forall t n : nat,
 (n <= size ->
  BV_to_nat (app (strip (R1 n) (size - n)) (R2 n)) =
  BV_to_nat V2 * BV_to_nat (trunc V1 n)) ->
 S n <= size ->
 n <= size ->
 BV_to_nat
   (app
      (strip
         (app (highs (R1 n))
            (Mux true (abit (BV_full_adder_sum (R2 n) V2 false) 0)
               (cons (lowbit (R2 n)) nil))) (size - S n))
      (app (highs (Mux true (BV_full_adder_sum (R2 n) V2 false) (R2 n)))
         (Mux true (cons (BV_full_adder_carry (R2 n) V2 false) nil)
            (cons false nil)))) =
 BV_to_nat V2 * BV_to_nat (app (trunc V1 n) (cons true nil)).

intros. simpl in |- *. do 3 rewrite BV_to_nat_app2. simpl in |- *.
rewrite mult_plus_distr2.
rewrite
 (mult_plus_distr2 (BV_to_nat V2) (BV_to_nat (trunc V1 n))
    (power2 (length (trunc V1 n)) * 1)).
rewrite <- H. clear H. elim plus_n_O.
rewrite highs_is_strip. rewrite highs_is_strip.
rewrite length_trunc. rewrite length_strip.
 rewrite length_app. rewrite length_strip.
 rewrite length_strip. rewrite length_abit.
 rewrite length_R1. rewrite (plus_comm (size - 1)).
 replace (1 + (size - 1)) with size.
rewrite minus_minus_lem2. rewrite length_BV_full_adder_sum.
rewrite length_R2. rewrite strip_app.
 rewrite BV_to_nat_app2. rewrite strip_strip.
 rewrite length_strip. rewrite length_strip.
 rewrite length_R1. rewrite BV_to_nat_app2.
simpl in |- *. rewrite minus_Sn_m.
 rewrite (minus_le_O (size - S n) (size - 1)).
simpl in |- *. rewrite minus_minus_lem2.
 rewrite strip_O. rewrite length_strip.
 rewrite length_R1. rewrite minus_minus_lem2.
replace (power2 n + power2 n) with (power2 (S n)).
replace (power2 n * 1) with (power2 n).
 rewrite <- (mult_assoc_reverse (power2 (S n))).
rewrite <- power2_plus. simpl in |- *. rewrite <- power2_eq2. rewrite <- power2_eq2.
replace (S (n + (size - 1))) with (n + size).
repeat rewrite plus_assoc_reverse.
replace
 (power2 n * BV_to_nat (abit (BV_full_adder_sum (R2 n) V2 false) 0) +
  (power2 (S n) * BV_to_nat (strip (BV_full_adder_sum (R2 n) V2 false) 1) +
   power2 (n + size) * bool_to_nat (BV_full_adder_carry (R2 n) V2 false)))
 with (power2 n * BV_to_nat (R2 n) + BV_to_nat V2 * power2 n).
trivial with arith. rewrite plus_assoc. rewrite <- highs_is_strip.
 unfold abit in |- *. rewrite strip_O.
rewrite <- lowbit_is_trunc. rewrite BV_nat_lem1. rewrite power2_plus.
 rewrite (mult_assoc_reverse (power2 n)). rewrite <- mult_plus_distr2.
replace size with (length (BV_full_adder_sum (R2 n) V2 false)).
replace (bool_to_nat (BV_full_adder_carry (R2 n) V2 false)) with
 (BV_to_nat (cons (BV_full_adder_carry (R2 n) V2 false) nil)).
rewrite <- BV_to_nat_app2.
replace
 (app (BV_full_adder_sum (R2 n) V2 false)
    (cons (BV_full_adder_carry (R2 n) V2 false) nil)) with
 (BV_full_adder (R2 n) V2 false).
rewrite BV_full_adder_ok.
 rewrite mult_plus_distr2. rewrite mult_plus_distr2.
simpl in |- *. elim mult_n_O. elim plus_n_O. rewrite (mult_sym (BV_to_nat V2)).
 trivial with arith. unfold BV_full_adder in |- *. trivial with arith.
simpl in |- *. elim plus_n_O. trivial with arith. rewrite length_BV_full_adder_sum; auto with arith.
rewrite length_R2; lia. rewrite length_V2_size. apply length_R2. assumption. rewrite length_BV_full_adder_sum.
rewrite length_R2. lia. assumption.
rewrite length_R2. rewrite length_V2_size; auto with arith. assumption.
apply not_nil; auto with arith. rewrite length_BV_full_adder_sum; auto with arith.
 rewrite length_R2; auto with arith. rewrite length_R2; auto with arith.
replace (S (n + (size - 1))) with (S n + (size - 1)).
replace (S n + (size - 1)) with (n + S (size - 1)).
rewrite minus_Sn_m. simpl in |- *. elim minus_n_O. trivial with arith. lia.
rewrite plus_comm. simpl in |- *. rewrite plus_comm. trivial with arith.
simpl in |- *. trivial with arith. rewrite mult_sym. simpl in |- *. elim plus_n_O.
trivial with arith. auto with arith. exact H1. exact H1. rewrite length_R1; auto with arith.
lia.
 exact H1. apply le_minus_minus. auto with arith. exact H0. exact H1.
rewrite length_R1. lia. exact H1. rewrite length_R1; auto with arith.
exact H1.
rewrite length_R2; auto with arith. exact H0. simpl in |- *. rewrite minus_Sn_m.
auto with arith. lia. exact H1. rewrite length_BV_full_adder_sum; auto with arith.
unfold lt in |- *. rewrite length_R2. lia. exact H1. transitivity size; auto with arith.
rewrite length_R2; auto.
rewrite length_BV_full_adder_sum; auto with arith. rewrite length_R2; try lia.
 rewrite length_R2; try lia. rewrite length_V2_size. reflexivity. rewrite length_R1; auto with arith. lia.
rewrite length_app. rewrite length_strip.
rewrite length_R1; try lia. rewrite length_R1. lia. auto. rewrite length_V1_size. auto. auto.
Qed.

Lemma app_trunc_abit:
 forall (v : BoolList) (i : nat),
 (***********************)
 S i <= length v -> trunc v i ++ abit v i = trunc v (S i).
simple induction v. unfold abit in |- *. simpl in |- *. trivial with arith.
simple induction i. simpl in |- *. unfold abit in |- *. rewrite trunc_O.
rewrite strip_O. simpl in |- *. rewrite trunc_O. trivial with arith.
intros. simpl in |- *. unfold abit in |- *.
rewrite strip_cons_S. unfold abit in H. rewrite H. trivial with arith.
generalize H1. simpl in |- *. auto with arith.
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

Lemma le_length_trunc :
 forall (v : BoolList) (i : nat), length (trunc v i) <= i.
(********************)
simple induction v. simpl in |- *. auto with arith.
intros. case i. rewrite trunc_O. auto with arith.
intro. simpl in |- *. apply le_n_S. apply H.
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

Lemma strip_trunc_i :
 forall (v : BoolList) (i : nat), strip (trunc v i) i = nil.
(******************)
simple induction v. auto with arith.
simple induction i. auto with arith.
intros. simpl in |- *. rewrite strip_cons_S. apply H.
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

Lemma R1_lem :
 forall t : nat, (* R1(t)[0:n-1-t]=B[t:n-1] *)
 t <= size -> trunc (R1 t) (size - t) = strip V1 t.
simple induction t. elim minus_n_O. rewrite <- (length_R1 0).
intro. rewrite trunc_all. rewrite strip_O. auto with arith.
auto with arith. intros. rewrite R1_eq2. rewrite highs_is_strip.
rewrite trunc_app. rewrite trunc_strip.
rewrite length_strip. rewrite length_R1.
replace (size - S n - (size - 1)) with 0.
rewrite trunc_O.
replace (1 + (size - S n)) with (size - n).
rewrite app_v_nil.
rewrite H. rewrite strip_strip. rewrite plus_comm. simpl in |- *. auto with arith.
apply le_Sn_le; exact H0.
simpl in |- *. rewrite minus_Sn_m. simpl in |- *. trivial with arith.
exact H0.
symmetry  in |- *. apply minus_le_O. apply le_minus_minus. auto with arith.
apply le_Sn_le; exact H0.
rewrite length_R1. lia. lia.
Qed.

Lemma R1_lem3 :
 forall t : nat, (* R1(t)[0]=B[t] *)
 t < size -> abit (R1 t) 0 = abit V1 t.
intros. unfold abit in |- *.
apply trunc_plus_petit with (size - t).
unfold lt in H. inversion H. rewrite <- minus_Sn_m. auto with arith. auto with arith.
rewrite <- minus_Sn_m. auto with arith. apply le_Sn_le; auto with arith.
rewrite strip_O. apply R1_lem. apply lt_le_weak. exact H.
Qed.

Lemma Invariant :
 forall t : nat,
 t <= size ->
 BV_to_nat (app (strip (R1 t) (size - t)) (R2 t)) =
 BV_to_nat V2 * BV_to_nat (trunc V1 t).

simple induction t. intros. elim minus_n_O. apply Invariant_t_O.
intros. rewrite <- app_trunc_abit.
replace (abit V1 n) with (abit V1 n).
rewrite <- (R1_lem3 n). rewrite R1_eq2. rewrite R2_eq2.
rewrite <- lowbit_is_abit. case (lowbit (R1 n)).
replace (cons (lowbit (BV_full_adder_sum (R2 n) V2 false)) nil) with
 (abit (BV_full_adder_sum (R2 n) V2 false) 0).
apply inv_ind_true. auto with arith.
intros. apply H. exact H1. exact H0.
apply le_Sn_le; exact H0. unfold abit in |- *. rewrite lowbit_is_trunc.
rewrite strip_O. trivial with arith.
apply not_nil. rewrite length_BV_full_adder_sum. rewrite length_R2.
exact size_not_O. apply le_Sn_le; exact H0.
rewrite length_R2. rewrite length_V2_size. trivial with arith.
apply le_Sn_le; exact H0.
replace (cons (lowbit (BV_full_adder_sum (R2 n) V2 false)) nil) with
 (abit (BV_full_adder_sum (R2 n) V2 false) 0).
apply inv_ind_false. trivial with arith.
exact H. exact H0. apply le_Sn_le; exact H0. rewrite lowbit_is_trunc.
unfold abit in |- *. rewrite strip_O. trivial with arith.
apply not_nil.
rewrite length_BV_full_adder_sum. rewrite length_R2; auto with arith.
transitivity size.
rewrite length_R2; trivial with arith. apply le_Sn_le; exact H0. auto with arith.
apply not_nil. rewrite length_R1; auto with arith. auto with arith. auto with arith.
rewrite length_V1_size. exact H0.
Qed.

Theorem Correct :
 BV_to_nat (app (R1 size) (R2 size)) = BV_to_nat V2 * BV_to_nat V1.

intros. rewrite <- (strip_O (R1 size)).
replace (BV_to_nat V1) with (BV_to_nat (trunc V1 size)).
rewrite (minus_n_n size). apply Invariant. auto with arith.
rewrite <- length_V1_size. rewrite trunc_all. trivial with arith.
Qed.

(******************************************************************)
Parameter a_size d_size : nat.  (* address and data sizes *)

Parameter di_init cx_init al_init : BoolList.

Definition addr := nat.
Inductive Memo : Type :=
| nilm : Memo
| consm : BoolList -> Memo -> Memo.
Fixpoint MemoSize (l: Memo): nat :=
  match l with
  | nilm => O
  | consm _ l' => S (MemoSize l')
  end.
Fixpoint MemoEmpty (n: nat) (v: BoolList) : Memo :=
  match n with
  | O => nilm
  | S n' => consm v (MemoEmpty n' v)
  end.
Fixpoint MemoZone (m: Memo) (a: addr) (l: nat): Memo :=
  match m with
  | nilm => nilm
  | consm headm tailm =>
      match a with
      | O =>
          match l with
          | O => consm headm nilm
          | S l' => consm headm (MemoZone tailm a l')
          end
      | S a' => MemoZone tailm a' l
      end
  end.

Fixpoint MemoRead (m: Memo) (a: addr): Memo :=
  match m with
  | nilm => nilm
  | consm headm tailm =>
      match a with
      | O => consm headm nilm
      | S a' => MemoRead tailm a'
      end
  end.

Fixpoint MemoWrite (m: Memo) (a: addr) (bv: BoolList): Memo :=
  match m with
  | nilm => nilm
  | consm headm tailm =>
      match a with
      | O => consm bv tailm
      | S a' => consm headm (MemoWrite tailm a' bv)
      end
  end.

Definition MMemo (v: BoolList) : Memo := consm v nilm.

Lemma read_write:
  forall (m: Memo) (a: addr) (v: BoolList),
    a < MemoSize m -> MemoRead (MemoWrite m a v) a = MMemo v.
  induction m.
  { intros. simpl in H. inversion H. }
  { induction a.
    { intros. simpl. unfold MMemo. reflexivity. }
    { intros. simpl.
      apply IHm. simpl in H. apply lt_S_n. assumption. }
  }
Qed.

Parameter mem_init : Memo.

Axiom di_initsize : length di_init = a_size.
Axiom cx_initsize : length cx_init = a_size.
Axiom al_initsize : length al_init = d_size.
Axiom mem_initsize : MemoSize mem_init = a_size.

Fixpoint IsNull (v : BoolList) : bool :=
  match v return bool with
  | nil => true
  | cons b w =>
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

Lemma IsNull_null : forall n : nat, IsNull (BV_null n) = true.
simple induction n. simpl in |- *. trivial.
intros. simpl in |- *. exact H.
Qed.

Lemma IsNull_BV_null :
 forall v : BoolList, IsNull v = true -> v = BV_null (length v).
simple induction v. simpl in |- *. unfold BV_null in |- *. auto.
intros a l H. intro.
change (cons a l = cons false (BV_null (length l))) in |- *.
rewrite <- H. generalize H0. replace a with false. trivial.
symmetry  in |- *. apply IsNull_false with (v := l). exact H0.
apply IsNull_cons with (a := a). exact H0.
Qed.

Parameter DC_a : BoolList.	Axiom DC_asize : length DC_a = a_size.
Parameter DC_d : BoolList.	Axiom DC_dsize : length DC_d = d_size.
Fixpoint BV_increment (l : BoolList) : BoolList :=
  match l with
  | nil => nil
  | cons false v => cons true v
  | cons true v => cons false (BV_increment v)
  end.


Fixpoint BV_increment_carry (l : BoolList) : bool :=
  match l with
  | nil => true
  | cons false v => false
  | cons true v => BV_increment_carry v
  end.



Fixpoint BV_decrement (l : BoolList) : BoolList :=
  match l with
  | nil => nil
  | cons false v => cons true (BV_decrement v)
  | cons true v => cons false v
  end.

Fixpoint BV_decrement_carry (l : BoolList) : bool :=
  match l with
  | nil => true
  | cons false v => BV_decrement_carry v
  | cons true v => false
  end.

Fixpoint di (st : nat) : BoolList -> BoolList -> BoolList -> Memo -> BoolList :=
  fun (di0 cx0 al0 : BoolList) (mem0 : Memo) =>
  match st return BoolList with
  | O => di0
  | S t =>
      match IsNull (cx t di0 cx0 al0 mem0) return BoolList with
      | true => di t di0 cx0 al0 mem0
      | false => BV_increment (di t di0 cx0 al0 mem0)
      end
  end

 with cx (st : nat) : BoolList -> BoolList -> BoolList -> Memo -> BoolList :=
  fun (di0 cx0 al0 : BoolList) (mem0 : Memo) =>
  match st return BoolList with
  | O => cx0
  | S t =>
      match IsNull (cx t di0 cx0 al0 mem0) return BoolList with
      | true => cx t di0 cx0 al0 mem0
      | false => BV_decrement (cx t di0 cx0 al0 mem0)
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
            (BV_to_nat (di t di0 cx0 al0 mem0)) (al t di0 cx0 al0 mem0)
      end
  end.

(****************************************************************)
(* Valeurs generales des registres *)

Lemma di_t :
 forall (t : nat) (di0 cx0 al0 : BoolList) (mem0 : Memo),
 di (S t) di0 cx0 al0 mem0 =
 match IsNull (cx t di0 cx0 al0 mem0) return BoolList with
 | true => di t di0 cx0 al0 mem0
 | false => BV_increment (di t di0 cx0 al0 mem0)
 end.
auto.
Qed.

Lemma cx_t :
 forall (t : nat) (di0 cx0 al0 : BoolList) (mem0 : Memo),
 cx (S t) di0 cx0 al0 mem0 =
 match IsNull (cx t di0 cx0 al0 mem0) return BoolList with
 | true => cx t di0 cx0 al0 mem0
 | false => BV_decrement (cx t di0 cx0 al0 mem0)
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
     MemoWrite (mem t di0 cx0 al0 mem0) (BV_to_nat (di t di0 cx0 al0 mem0))
       (al t di0 cx0 al0 mem0)
 end.
auto.
Qed.

Lemma length_BV_increment :
 forall v : BoolList, length (BV_increment v) = length v.
simple induction v. auto.
simple induction b.
simpl in |- *. intros. rewrite H; trivial.
simpl in |- *. intros. trivial.
Qed.

Lemma length_BV_decrement :
 forall v : BoolList, length (BV_decrement v) = length v.
simple induction v. auto.
simple induction b.
simpl in |- *. intros. trivial.
simpl in |- *. intros. rewrite H; trivial.
Qed.

(****************************************************************)
(* Longueurs des registres *)

Lemma length_di :
 forall t : nat, length (di t di_init cx_init al_init mem_init) = a_size.
simple induction t. simpl in |- *. exact di_initsize.
intros.
rewrite di_t. elim (IsNull (cx n di_init cx_init al_init mem_init)). exact H.
rewrite length_BV_increment. exact H.
Qed.

Lemma length_cx :
 forall t : nat, length (cx t di_init cx_init al_init mem_init) = a_size.
simple induction t. simpl in |- *. exact cx_initsize.
intros.
rewrite cx_t. elim (IsNull (cx n di_init cx_init al_init mem_init)). exact H.
rewrite length_BV_decrement. exact H.
Qed.

Lemma length_al :
 forall t : nat, length (al t di_init cx_init al_init mem_init) = d_size.
intro. rewrite al_constant. exact al_initsize.
Qed.

Definition di1 (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList) := di0.
Definition cx1 (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList) := cx0.
Definition al1 (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList) := al0.
Definition mem1 (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList) := mem0.
Definition ad1 (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList) := di0.
Definition da1 (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList) := al0.

Definition compo_2_1_BV
  (f : nat -> BoolList -> BoolList -> BoolList -> Memo -> BoolList -> BoolList -> BoolList)
  (t : nat) (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList) :=
  f t (di1 di0 cx0 al0 mem0 ad0 da0) (cx1 di0 cx0 al0 mem0 ad0 da0)
    (al1 di0 cx0 al0 mem0 ad0 da0) (mem1 di0 cx0 al0 mem0 ad0 da0)
    (ad1 di0 cx0 al0 mem0 ad0 da0) (da1 di0 cx0 al0 mem0 ad0 da0).
Definition compo_2_1_Memo
  (f : nat -> BoolList -> BoolList -> BoolList -> Memo -> BoolList -> BoolList -> Memo)
  (t : nat) (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList) :=
  f t (di1 di0 cx0 al0 mem0 ad0 da0) (cx1 di0 cx0 al0 mem0 ad0 da0)
    (al1 di0 cx0 al0 mem0 ad0 da0) (mem1 di0 cx0 al0 mem0 ad0 da0)
    (ad1 di0 cx0 al0 mem0 ad0 da0) (da1 di0 cx0 al0 mem0 ad0 da0).
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
      | false => BV_decrement (cx2 t di0 cx0 al0 mem0 ad0 da0)
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
            (BV_to_nat (ad2 t di0 cx0 al0 mem0 ad0 da0))
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
      | false => BV_increment (ad2 t di0 cx0 al0 mem0 ad0 da0)
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

Definition di_2_1 := compo_2_1_BV di2.
Definition cx_2_1 := compo_2_1_BV cx2.
Definition al_2_1 := compo_2_1_BV al2.
Definition mem_2_1 := compo_2_1_Memo mem2.
Definition ad_2_1 := compo_2_1_BV ad2.
Definition da_2_1 := compo_2_1_BV da2.

Definition compo'_BV (f : BoolList -> BoolList -> BoolList -> Memo -> BoolList -> BoolList -> BoolList)
  (t : nat) (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList) :=
  f (di_2_1 t di0 cx0 al0 mem0 ad0 da0) (cx_2_1 t di0 cx0 al0 mem0 ad0 da0)
    (al_2_1 t di0 cx0 al0 mem0 ad0 da0) (mem_2_1 t di0 cx0 al0 mem0 ad0 da0)
    (ad_2_1 t di0 cx0 al0 mem0 ad0 da0) (da_2_1 t di0 cx0 al0 mem0 ad0 da0).
Definition compo'_Memo (f : BoolList -> BoolList -> BoolList -> Memo -> BoolList -> BoolList -> Memo)
  (t : nat) (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList) :=
  f (di_2_1 t di0 cx0 al0 mem0 ad0 da0) (cx_2_1 t di0 cx0 al0 mem0 ad0 da0)
    (al_2_1 t di0 cx0 al0 mem0 ad0 da0) (mem_2_1 t di0 cx0 al0 mem0 ad0 da0)
    (ad_2_1 t di0 cx0 al0 mem0 ad0 da0) (da_2_1 t di0 cx0 al0 mem0 ad0 da0).

Definition di3 (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList) := ad0.
Definition cx3 (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList) := cx0.
Definition al3 (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList) := al0.
Definition mem3 (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList) := mem0.
Definition ad3 (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList) := ad0.
Definition da3 (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList) := da0.

Definition di' := compo'_BV di3.
Definition cx' := compo'_BV cx3.
Definition al' := compo'_BV al3.
Definition mem' := compo'_Memo mem3.
Definition ad' := compo'_BV ad3.
Definition da' := compo'_BV da3.

Lemma cx2_t :
 forall (t : nat) (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList),
 cx2 (S t) di0 cx0 al0 mem0 ad0 da0 =
 match IsNull (cx2 t di0 cx0 al0 mem0 ad0 da0) return BoolList with
 | true => cx2 t di0 cx0 al0 mem0 ad0 da0
 | false => BV_decrement (cx2 t di0 cx0 al0 mem0 ad0 da0)
 end.
auto.
Qed.
Lemma cx_cx' :
 forall t : nat,
 cx t di_init cx_init al_init mem_init =
 cx' t di_init cx_init al_init mem_init DC_a DC_d.
unfold cx' in |- *. unfold compo'_BV in |- *. unfold cx3 in |- *. unfold cx_2_1, compo_2_1_BV in |- *.
unfold di1, cx1, al1, mem1, ad1, da1 in |- *. simple induction t. auto.
intros. rewrite cx_t. rewrite cx2_t. rewrite H. trivial.
Qed.

Lemma ad2_t :
 forall (t : nat) (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList),
 ad2 (S t) di0 cx0 al0 mem0 ad0 da0 =
 match IsNull (cx2 t di0 cx0 al0 mem0 ad0 da0) return BoolList with
 | true => ad2 t di0 cx0 al0 mem0 ad0 da0
 | false => BV_increment (ad2 t di0 cx0 al0 mem0 ad0 da0)
 end.
auto.
Qed.
Lemma di_di' :
 forall t : nat,
 di t di_init cx_init al_init mem_init =
 di' t di_init cx_init al_init mem_init DC_a DC_d.
unfold di' in |- *. unfold compo'_BV in |- *.
unfold di3 in |- *. unfold ad_2_1, compo_2_1_BV in |- *. unfold di1, cx1, al1, mem1, ad1, da1 in |- *.
simple induction t. auto.
intros. rewrite di_t. rewrite ad2_t. rewrite H.
replace (cx n di_init cx_init al_init mem_init) with
 (cx' n di_init cx_init al_init mem_init DC_a DC_d).
unfold cx', compo'_BV in |- *. unfold cx3 in |- *. unfold cx_2_1, compo_2_1_BV in |- *.
unfold di1, cx1, al1, mem1, ad1, da1 in |- *.
trivial. rewrite cx_cx'. trivial.
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

Lemma al_al' :
 forall t : nat,
 al t di_init cx_init al_init mem_init =
 al' t di_init cx_init al_init mem_init DC_a DC_d.
intro.
rewrite al_constant.
unfold al' in |- *.
unfold compo'_BV in |- *.
unfold al3 in |- *.
unfold al_2_1 in |- *.
unfold compo_2_1_BV in |- *.
rewrite al2_constant.
unfold al1 in |- *.
trivial.
Qed.

Lemma mem2_t :
 forall (t : nat) (di0 cx0 al0 : BoolList) (mem0 : Memo) (ad0 da0 : BoolList),
 mem2 (S t) di0 cx0 al0 mem0 ad0 da0 =
 match IsNull (cx2 t di0 cx0 al0 mem0 ad0 da0) return Memo with
 | true => mem2 t di0 cx0 al0 mem0 ad0 da0
 | false =>
     MemoWrite (mem2 t di0 cx0 al0 mem0 ad0 da0)
       (BV_to_nat (ad2 t di0 cx0 al0 mem0 ad0 da0))
       (da2 t di0 cx0 al0 mem0 ad0 da0)
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
Lemma mem_mem' :
 forall t : nat,
 mem t di_init cx_init al_init mem_init =
 mem' t di_init cx_init al_init mem_init DC_a DC_d.
unfold mem', compo'_Memo in |- *.
unfold mem3 in |- *.
unfold mem_2_1, compo_2_1_Memo in |- *.
unfold di1, cx1, al1, mem1, ad1, da1 in |- *.
simple induction t.
auto.

intros.
rewrite mem2_t.
rewrite mem_t.
rewrite H.
replace (al n di_init cx_init al_init mem_init) with al_init.
replace (da2 n di_init cx_init al_init mem_init di_init al_init) with al_init.
rewrite (di_di' n).
unfold di' in |- *.
unfold compo'_BV in |- *.
unfold di3 in |- *.
unfold ad_2_1, compo_2_1_BV in |- *.
unfold di1, cx1, al1, mem1, ad1, da1 in |- *.
rewrite (cx_cx' n).
unfold cx', compo'_BV, cx3 in |- *.
unfold cx_2_1, compo_2_1_BV in |- *.
unfold di1, cx1, al1, mem1, ad1, da1 in |- *.
trivial.

rewrite da2_constant.
trivial.

rewrite al_constant.
trivial.
Qed.

Theorem Fill_ok :
 forall t : nat,
 di t di_init cx_init al_init mem_init =
 di' t di_init cx_init al_init mem_init DC_a DC_d /\
 cx t di_init cx_init al_init mem_init =
 cx' t di_init cx_init al_init mem_init DC_a DC_d /\
 al t di_init cx_init al_init mem_init =
 al' t di_init cx_init al_init mem_init DC_a DC_d /\
 mem t di_init cx_init al_init mem_init =
 mem' t di_init cx_init al_init mem_init DC_a DC_d.
split. apply di_di'.
split. apply cx_cx'.
split. apply al_al'. apply mem_mem'.
Qed.
