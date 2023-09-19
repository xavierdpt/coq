Set Implicit Arguments.

Local Notation PropositionalExtensionality :=
  (forall A B : Prop, (A <-> B) -> A = B).

Local Notation ProvablePropositionExtensionality :=
  (forall A:Prop, A -> A = True).

Local Notation PredicateExtensionality :=
  (forall (A:Type) (P Q : A -> Prop), (forall x, P x <-> Q x) -> P = Q).

Local Notation PropositionalFunctionalExtensionality :=
  (forall (A:Type) (P Q : A -> Prop), (forall x, P x = Q x) -> P = Q).

Lemma PredExt_imp_PropFunExt : PredicateExtensionality -> PropositionalFunctionalExtensionality.
Proof.
  intro h.
  intro A.
  specialize (h A).
  intros P Q.
  specialize (h P Q).
  intro h'.
  apply h.
  clear h.
  intro x.
  specialize (h' x).
  rewrite h'.
  split;intro;assumption.
Qed.

Lemma PropExt_imp_ProvPropExt : PropositionalExtensionality -> ProvablePropositionExtensionality.
Proof.
  intro h.
  intro P.
  specialize (h P True).
  intro hp.
  apply h. clear h.
  split.
  intros _. trivial.
  intros _. assumption.
Qed.
