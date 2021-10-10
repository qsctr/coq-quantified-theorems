Require Import Nat Arith.

Inductive Lst : Type := cons : nat -> Lst -> Lst |  nil : Lst.

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

Theorem theorem0 : forall (_t_2 : Lst) (_t_1 : nat), eq (rev (append (rev _t_2) (cons _t_1 nil))) (cons _t_1 _t_2).
Proof.
Admitted.

