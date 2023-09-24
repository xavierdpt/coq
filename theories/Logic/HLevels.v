Require Import Coq.Logic.FunctionalExtensionality.

Definition IsHProp (P : Type) : Prop
  := forall p q : P, p = q.

Lemma forall_hprop : forall (A : Type) (P : A -> Prop),
    (forall x:A, IsHProp (P x))
    -> IsHProp (forall x:A, P x).
Proof.
  intros A P H p q. apply functional_extensionality_dep.
  intro x. apply H.
Qed.

Lemma and_hprop : forall P Q : Prop,
    IsHProp P -> IsHProp Q -> IsHProp (P /\ Q).
Proof.
  intros. intros p q. destruct p,q.
  replace p0 with p.
  - replace q0 with q.
    + reflexivity.
    + apply H0.
  - apply H.
Qed.

Lemma impl_hprop : forall P Q : Prop,
    IsHProp Q -> IsHProp (P -> Q).
Proof.
  intros P Q H p q. apply functional_extensionality.
  intros. apply H.
Qed.

Lemma not_hprop : forall P : Type, IsHProp (P -> False).
Proof.
  intros P p q. apply functional_extensionality.
  intros. contradiction.
Qed.
