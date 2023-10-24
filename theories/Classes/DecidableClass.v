Class Decidable (P : Prop) := {
  Decidable_witness : bool;
  Decidable_spec : Decidable_witness = true <-> P
}.

Lemma Decidable_sound : forall P (H : Decidable P),
  Decidable_witness = true -> P.
Proof.
  intros P H.
  intro heq.
  apply Decidable_spec.
  exact heq.
Qed.

Lemma Decidable_complete : forall P (H : Decidable P),
  P -> Decidable_witness = true.
Proof.
  intros P H.
  intro h.
  apply Decidable_spec.
  exact h.
Qed.

Lemma Decidable_sound_alt : forall P (H : Decidable P),
   ~ P -> Decidable_witness = false.
Proof.
  intros P H.
  intro hpf.
  destruct H as [ witness h ].
  simpl.
  destruct witness.
  {
    exfalso.
    apply hpf.
    apply -> h.
    reflexivity.
  }
  { reflexivity. }
Qed.

Lemma Decidable_complete_alt : forall P (H : Decidable P),
  Decidable_witness = false -> ~ P.
Proof.
  intros P H heq.
  red.
  intro hp.
  destruct H as [ witness h].
  simpl in heq.
  destruct h as [ hl hr ].
  subst witness.
  specialize (hr hp).
  inversion hr.
Qed.

Definition decide P {H : Decidable P} := @Decidable_witness _ H.

(*
Ltac _decide_ P H :=
  let b := fresh "b" in
  set (b := decide P) in *;
  assert (H : decide P = b) by reflexivity;
  clearbody b;
  destruct b; [apply Decidable_sound in H|apply Decidable_complete_alt in H].

*)
