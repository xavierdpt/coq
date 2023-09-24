Axiom functional_extensionality_dep : forall {A} {B : A -> Type},
  forall (f g : forall x : A, B x),
  (forall x, f x = g x) -> f = g.

Lemma functional_extensionality {A B} (f g : A -> B) :
  (forall x, f x = g x) -> f = g.
Proof.
  apply functional_extensionality_dep.
Qed.

(** Extensionality of [forall]s follows from functional extensionality. *)
Lemma forall_extensionality {A} {B C : A -> Type} (H : forall x : A, B x = C x)
: (forall x, B x) = (forall x, C x).
Proof.
  apply functional_extensionality in H.
  destruct H.
  reflexivity.
Defined.

Lemma forall_extensionalityP {A} {B C : A -> Prop} (H : forall x : A, B x = C x)
: (forall x, B x) = (forall x, C x).
Proof.
  apply functional_extensionality in H.
  destruct H.
  reflexivity.
Defined.

Lemma forall_extensionalityS {A} {B C : A -> Set} (H : forall x : A, B x = C x)
: (forall x, B x) = (forall x, C x).
Proof.
  apply functional_extensionality in H.
  destruct H.
  reflexivity.
Defined.

Tactic Notation "extensionality" ident(x) :=
  match goal with
    [ |- ?X = ?Y ] =>
    (apply (@functional_extensionality _ _ X Y) ||
     apply (@functional_extensionality_dep _ _ X Y) ||
     apply forall_extensionalityP ||
     apply forall_extensionalityS ||
     apply forall_extensionality) ; intro x
  end.
