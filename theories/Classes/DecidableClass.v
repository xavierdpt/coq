(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * A typeclass to ease the handling of decidable properties. *)

(** A proposition is decidable whenever it is reflected by a boolean. *)


Class Decidable (P : Prop) := {
  Decidable_witness : bool;
  Decidable_spec : Decidable_witness = true <-> P
}.

(** Alternative ways of specifying the reflection property. *)

Lemma Decidable_sound : forall P (H : Decidable P),
  Decidable_witness = true -> P.
Proof.
  intros P H.
  intro heq.
  apply -> Decidable_spec.
  exact heq.
Qed.

Lemma Decidable_complete : forall P (H : Decidable P),
  P -> Decidable_witness = true.
Proof.
  intros P H.
  intro h.
  apply <- Decidable_spec.
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

(** The generic function that should be used to program, together with some
  useful tactics. *)

Definition decide P {H : Decidable P} := @Decidable_witness _ H.

Ltac _decide_ P H :=
  let b := fresh "b" in
  set (b := decide P) in *;
  assert (H : decide P = b) by reflexivity;
  clearbody b;
  destruct b; [apply Decidable_sound in H|apply Decidable_complete_alt in H].

Tactic Notation "decide" constr(P) "as" ident(H) :=
  _decide_ P H.

Tactic Notation "decide" constr(P) :=
  let H := fresh "H" in _decide_ P H.

(** Some usual instances. *)

#[global,refine]
Instance Decidable_not {P} `{Decidable P} : Decidable (~ P) := {
  Decidable_witness := negb Decidable_witness
}.
Proof.
  destruct H as [ witness h ].
  simpl.
  destruct h as [ hl hr ].
  destruct witness.
  all:simpl.
  split.
  { intro h. inversion h. }
  { intro hpf. red in hpf. exfalso. apply hpf. apply hl. reflexivity. }
  split.
  { intros _. red. intro hp. specialize (hr hp). inversion hr. }
  { intros _. reflexivity. }
Defined.
