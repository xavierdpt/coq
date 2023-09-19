(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(** Properties of decidable propositions *)

Definition decidable (P:Prop) := P \/ ~ P.

Theorem dec_not_not : forall P:Prop, decidable P -> (~ P -> False) -> P.
Proof.
intro P.
intro h.
unfold decidable in h.
destruct h as [ hl | hr ].
intros _. assumption.
intro h. exfalso. apply h. assumption.
Qed.

Theorem dec_True : decidable True.
Proof.
unfold decidable. left. trivial.
Qed.

Theorem dec_False : decidable False.
Proof.
red. right. unfold not. intro f. assumption.
Qed.

Theorem dec_or :
 forall A B:Prop, decidable A -> decidable B -> decidable (A \/ B).
Proof.
intros A B ha hb.
red in ha, hb.
red.
destruct ha as [ hal | har ] ; destruct hb as [ hbl | hbr ].
left. left. assumption.
left. left. assumption.
left. right. assumption.
right. unfold not. intro h.
destruct h as [ hl | hr ].
apply har. assumption.
apply hbr. assumption.
Qed.

Theorem dec_and :
 forall A B:Prop, decidable A -> decidable B -> decidable (A /\ B).
Proof.
intros A B ha hb.
red in ha, hb.
red.
destruct ha as [ hal | har ] ; destruct hb as [ hbl | hbr ].
left. split;assumption.
all:right.
all:red.
all:intros [ ha hb ].
apply hbr;assumption.
apply har;assumption.
apply har;assumption.
Qed.

Theorem dec_not : forall A:Prop, decidable A -> decidable (~ A).
Proof.
intros A h.
red.
red in h.
destruct h as [ hl | hr ].
right. unfold not. intro haf. apply haf. assumption.
left. assumption.
Qed.

Theorem dec_imp :
 forall A B:Prop, decidable A -> decidable B -> decidable (A -> B).
Proof.
intros A B ha hb.
red.
red in ha, hb.
destruct ha as [ hal | har ];
destruct hb as [ hbl | hbr ].
left. intros _. assumption.
right. red. intro hab. red in hbr. apply hbr. apply hab. assumption.
left. intros _. assumption.
left. intro ha. exfalso. apply har. assumption.
Qed.

Theorem dec_iff :
 forall A B:Prop, decidable A -> decidable B -> decidable (A<->B).
Proof.
intros A B ha hb.
red.
red in ha, hb.
destruct ha as [ hal | har ];
destruct hb as [ hbl | hbr ].
left. split ; intro x ; assumption.
right. intros [ hab hba ]. apply hbr. apply hab. assumption.
right. intros [ hab hba ]. apply har. apply hba. assumption.
left. split. all:intro h. all:exfalso.
apply har. assumption.
apply hbr. assumption.
Qed.

Theorem not_not : forall P:Prop, decidable P -> ~ ~ P -> P.
Proof.
intros P h.
red in h.
destruct h as [ hl | hr ].
intros _. assumption.
intro h. unfold not in *.
exfalso. apply h. assumption.
Qed.

Theorem not_or : forall A B:Prop, ~ (A \/ B) -> ~ A /\ ~ B.
Proof.
intros A B h.
red in h.
split.
all:red.
all:intro h'.
all:apply h.
left. assumption.
right. assumption.
Qed.

Theorem not_and : forall A B:Prop, decidable A -> ~ (A /\ B) -> ~ A \/ ~ B.
Proof.
intros A B h.
red in h.
destruct h as [ hl | hr ].
all:unfold not.
all:intro h.
right. intro hb. apply h. split;assumption.
left. red in hr. assumption.
Qed.

Theorem not_imp : forall A B:Prop, decidable A -> ~ (A -> B) -> A /\ ~ B.
Proof.
intros A B h.
red in h.
destruct h as [ hl | hr ].
all:unfold not.
all:intro h.
all:split.
assumption.
intro hb. apply h. intros _. assumption.
red in hr. exfalso. apply h. intro ha. exfalso. apply hr. exact ha.
intro hb. apply h. intros _. assumption.
Qed.

Theorem imp_simp : forall A B:Prop, decidable A -> (A -> B) -> ~ A \/ B.
Proof.
intros A B h.
red in h.
destruct h as [ hl | hr ].
all:intro hab.
right. apply hab. assumption.
left. assumption.
Qed.

Theorem not_iff :
  forall A B:Prop, decidable A -> decidable B ->
    ~ (A <-> B) -> (A /\ ~ B) \/ (~ A /\ B).
Proof.
intros A B ha hb.
red in ha, hb.
intro h.
red in h.
destruct ha as [ hal | har ];
destruct hb as [ hbl | hbr ].
exfalso. apply h. split;intros _;assumption.
left. split;assumption.
right. split;assumption.
exfalso. apply h. split.
all:intro hx.
all:exfalso.
apply har. assumption.
apply hbr. assumption.
Qed.

Register dec_True as core.dec.True.
Register dec_False as core.dec.False.
Register dec_or as core.dec.or.
Register dec_and as core.dec.and.
Register dec_not as core.dec.not.
Register dec_imp as core.dec.imp.
Register dec_iff as core.dec.iff.
Register dec_not_not as core.dec.not_not.
Register not_not as core.dec.dec_not_not.
Register not_or as core.dec.not_or.
Register not_and as core.dec.not_and.
Register not_imp as core.dec.not_imp.
Register imp_simp as core.dec.imp_simp.
Register not_iff as core.dec.not_iff.

(** Results formulated with iff, used in FSetDecide.
    Negation are expanded since it is unclear whether setoid rewrite
    will always perform conversion. *)

(** We begin with lemmas that, when read from left to right,
    can be understood as ways to eliminate uses of [not]. *)

Theorem not_true_iff : (True -> False) <-> False.
Proof.
split.
intro h. apply h. trivial.
intro f. destruct f.
Qed.

Theorem not_false_iff : (False -> False) <-> True.
Proof.
split.
intros _. trivial.
intros _. intro;assumption.
Qed.

Theorem not_not_iff : forall A:Prop, decidable A ->
  (((A -> False) -> False) <-> A).
Proof.
intros A h.
red in h.
destruct h as [ hl | hr ].
all:split.
all:intro h.
assumption.
intro haf. apply haf. assumption.
red in hr. exfalso. apply h. assumption.
exfalso. apply hr. assumption.
Qed.

Theorem contrapositive : forall A B:Prop, decidable A ->
  (((A -> False) -> (B -> False)) <-> (B -> A)).
Proof.
intros A B ha.
red in ha.
split.
intro h. intro hb.
destruct ha as [ hal | har ].
assumption.
exfalso. apply h. assumption. assumption.
intro hba. intro haf. intro hb. apply haf. apply hba. assumption.
Qed.

Lemma or_not_l_iff_1 : forall A B: Prop, decidable A ->
  ((A -> False) \/ B <-> (A -> B)).
Proof.
intros A B ha.
red in ha.
destruct ha as [ hal | har ].
all:split.
intro h. intros _.
destruct h as [ hl | hr ].
exfalso. apply hl. assumption. assumption.
intro hab. right. apply hab. assumption.
intro h. intro ha. exfalso. apply har. assumption.
intro hab. left. assumption.
Qed.

Lemma or_not_l_iff_2 : forall A B: Prop, decidable B ->
  ((A -> False) \/ B <-> (A -> B)).
Proof.
intros A B hb.
red in hb.
destruct hb as [ hbl | hbr ].
all:split.
intro h. intros ha. assumption.
intros hab. right. assumption.
intro h. intro ha. destruct h as [ hl | hr ].
exfalso. apply hl. assumption. assumption.
intro hab. left. intro ha. apply hbr. apply hab. assumption.
Qed.

Lemma or_not_r_iff_1 : forall A B: Prop, decidable A ->
  (A \/ (B -> False) <-> (B -> A)).
Proof.
intros A B ha.
red in ha.
destruct ha as [ hal | har ].
all:split.
intro h. intro hb. assumption.
intro hba. left. assumption.
intro h. intro hb. destruct h as [ ha | hbf ]. assumption. exfalso. apply hbf. assumption.
intro hba. right. intro hb. apply har. apply hba. assumption.
Qed.

Lemma or_not_r_iff_2 : forall A B: Prop, decidable B ->
  (A \/ (B -> False) <-> (B -> A)).
Proof.
intros A B hb.
red in hb.
destruct hb as [ hbl | hbr ].
all:split.
intro h. intros _. destruct h as [ ha | hbf ]. assumption. exfalso. apply hbf. assumption.
intro hba. left. apply hba. assumption.
intro h. intro hb. exfalso. apply hbr. assumption.
intro hba. right. assumption.
Qed.

Lemma imp_not_l : forall A B: Prop, decidable A ->
  (((A -> False) -> B) <-> (A \/ B)).
Proof.
intros A B ha.
red in ha.
destruct ha as [ hal | har ].
all:split.
intro h. left. assumption.
intro h. intro haf. exfalso. apply haf. assumption.
intro h. right. apply h. assumption.
intro h. intros _. destruct h as [ ha | hb ]. exfalso. apply har. assumption. assumption.
Qed.


(** Moving Negations Around:
    We have four lemmas that, when read from left to right,
    describe how to push negations toward the leaves of a
    proposition and, when read from right to left, describe
    how to pull negations toward the top of a proposition. *)

Theorem not_or_iff : forall A B:Prop,
  (A \/ B -> False) <-> (A -> False) /\ (B -> False).
Proof.
intros A B.
split.
intros h. split.
intro ha. apply h. left. assumption.
intro hb. apply h. right. assumption.
intros [ haf hbf ].
intros [ ha | hb ].
apply haf. assumption.
apply hbf. assumption.
Qed.

Lemma not_and_iff : forall A B:Prop,
  (A /\ B -> False) <-> (A -> B -> False).
Proof.
intros A B.
split.
intros h. intros ha hb. apply h. split;assumption.
intro h. intros [ ha hb ]. apply h;assumption.
Qed.

Lemma not_imp_iff : forall A B:Prop, decidable A ->
  (((A -> B) -> False) <-> A /\ (B -> False)).
Proof.
intros A B ha.
red in ha.
destruct ha as [ ha | haf ].
all:split.
intro h.
split. assumption. intro hb. apply h. intros _. assumption.
intros [ _ hbf ]. intro hab. apply hbf. apply hab. assumption.
intro h. split. exfalso. apply h. intro ha. exfalso. apply haf. assumption.
intro hb. apply h. intro ha. assumption.
intros [ ha _ ]. exfalso. apply haf. assumption.
Qed.

Lemma not_imp_rev_iff : forall A B : Prop, decidable A ->
  (((A -> B) -> False) <-> (B -> False) /\ A).
Proof.
intros A B ha.
red in ha.
destruct ha as [ ha | haf ].
all:split.
intro h. split. intro hb. apply h. intros _. assumption. assumption.
intros [ hl hr ]. intro hab. apply hl. apply hab. assumption.
intro h. exfalso. apply h. intro ha. exfalso. apply haf. assumption.
intros [hbf ha]. intro hab. apply haf. assumption.
Qed.

(* Functional relations on decidable co-domains are decidable *)

Theorem dec_functional_relation :
  forall (X Y : Type) (A:X->Y->Prop), (forall y y' : Y, decidable (y=y')) ->
  (forall x, exists! y, A x y) -> forall x y, decidable (A x y).
Proof.
intros X Y A.
intro hdeq.
intro hu.
intros x y.
red.
specialize (hu x).
destruct hu as [ y' hu ].
red in hu.
destruct hu as [ haxy' heq ].
specialize (hdeq y y').
red in hdeq.
destruct hdeq as [ hl | hr ].
{ destruct hl. left. assumption. }
{ right. red. intro haxy. red in hr. apply hr. clear hr. symmetry. apply heq. assumption. }
Qed.

(** With the following hint database, we can leverage [auto] to check
    decidability of propositions. *)

#[global]
Hint Resolve dec_True dec_False dec_or dec_and dec_imp dec_not dec_iff
 : decidable_prop.

(** [solve_decidable using lib] will solve goals about the
    decidability of a proposition, assisted by an auxiliary
    database of lemmas.  The database is intended to contain
    lemmas stating the decidability of base propositions,
    (e.g., the decidability of equality on a particular
    inductive type). *)

Tactic Notation "solve_decidable" "using" ident(db) :=
  match goal with
   | |- decidable _ =>
     solve [ auto 100 with decidable_prop db ]
  end.

Tactic Notation "solve_decidable" :=
  solve_decidable using core.
