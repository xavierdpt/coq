Require Import Eqdep.

Set Implicit Arguments.

Unset Elimination Schemes.
Inductive JMeq (A:Type) (x:A) : forall B:Type, B -> Prop :=
    JMeq_refl : JMeq x x.
Set Elimination Schemes.


Theorem JMeq_eq : forall (A:Type) (x y:A), JMeq x y -> x = y.
Proof.
  intros A x y Heq.
  inversion Heq.
  now apply (inj_pairT2 _ _ A x y).
Qed.
