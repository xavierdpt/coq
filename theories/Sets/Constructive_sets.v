(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(****************************************************************************)
(*                                                                          *)
(*                         Naive Set Theory in Coq                          *)
(*                                                                          *)
(*                     INRIA                        INRIA                   *)
(*              Rocquencourt                        Sophia-Antipolis        *)
(*                                                                          *)
(*                                 Coq V6.1                                 *)
(*									    *)
(*			         Gilles Kahn 				    *)
(*				 Gerard Huet				    *)
(*									    *)
(*									    *)
(*                                                                          *)
(* Acknowledgments: This work was started in July 1993 by F. Prost. Thanks  *)
(* to the Newton Institute for providing an exceptional work environment    *)
(* in Summer 1995. Several developments by E. Ledinot were an inspiration.  *)
(****************************************************************************)

Require Export Ensembles.

Section Ensembles_facts.
  Variable U : Type.

  Lemma Extension : forall B C:Ensemble U, B = C -> Same_set U B C.
  Proof.
    intros B C heq.
    subst C.
    red.
    split.
    all:red.
    all:intro u.
    all:intro hin.
    all:exact hin.
  Qed.

  Lemma Noone_in_empty : forall x:U, ~ In U (Empty_set U) x.
  Proof.
    intro u.
    unfold not.
    intro hu.
    red in hu.
    destruct hu.
  Qed.

  Lemma Included_Empty : forall A:Ensemble U, Included U (Empty_set U) A.
  Proof.
    intro E.
    red.
    intro u.
    intro hin.
    red in hin.
    destruct hin.
  Qed.

  Lemma Add_intro1 :
    forall (A:Ensemble U) (x y:U), In U A y -> In U (Add U A x) y.
  Proof.
    intro E.
    intros x y.
    intro hin.
    red.
    red.
    apply Union_introl.
    exact hin.
  Qed.

  Lemma Add_intro2 : forall (A:Ensemble U) (x:U), In U (Add U A x) x.
  Proof.
    intros E x.
    red.
    red.
    apply Union_intror.
    red.
    apply In_singleton.
  Qed.

  Lemma Inhabited_add : forall (A:Ensemble U) (x:U), Inhabited U (Add U A x).
  Proof.
    intros E x.
    apply (Inhabited_intro _ _ x).
    red.
    red.
    right.
    red.
    constructor.
  Qed.

  Lemma Inhabited_not_empty :
    forall X:Ensemble U, Inhabited U X -> X <> Empty_set U.
  Proof.
    intros E h.
    red.
    intro heq.
    destruct h as [ x hin ].
    red in hin.
    subst E.
    destruct hin.
  Qed.

  Lemma Add_not_Empty : forall (A:Ensemble U) (x:U), Add U A x <> Empty_set U.
  Proof.
    intros E u.
    apply Inhabited_not_empty.
    apply Inhabited_add.
  Qed.

  Lemma not_Empty_Add : forall (A:Ensemble U) (x:U), Empty_set U <> Add U A x.
  Proof.
    intros E u.
    red.
    intro h.
    eapply Inhabited_not_empty.
    2:symmetry.
    2:exact h.
    apply Inhabited_add.
  Qed.

  Lemma Singleton_inv : forall x y:U, In U (Singleton U x) y -> x = y.
  Proof.
    intros x y h.
    red in h.
    destruct h.
    reflexivity.
  Qed.

  Lemma Singleton_intro : forall x y:U, x = y -> In U (Singleton U x) y.
  Proof.
    intros x y heq.
    subst y.
    red.
    constructor.
  Qed.

  Lemma Union_inv :
    forall (B C:Ensemble U) (x:U), In U (Union U B C) x -> In U B x \/ In U C x.
  Proof.
    intros B C x h.
    red in h.
    destruct h as [ u h | u h ].
    left. exact h.
    right. exact h.
  Qed.

  Lemma Add_inv :
    forall (A:Ensemble U) (x y:U), In U (Add U A x) y -> In U A y \/ x = y.
  Proof.
    intros E x y h.
    red in h.
    red in h.
    destruct h as [ u h | u h ].
    left. exact h.
    red in h. destruct h.
    right. reflexivity.
  Qed.

  Lemma Intersection_inv :
    forall (B C:Ensemble U) (x:U),
      In U (Intersection U B C) x -> In U B x /\ In U C x.
  Proof.
    intros B C u h.
    red in h.
    destruct h as [ u hl hr ].
    split;assumption.
  Qed.

  Lemma Couple_inv : forall x y z:U, In U (Couple U x y) z -> z = x \/ z = y.
  Proof.
    intros x y z h.
    red in h.
    destruct h.
    left;reflexivity.
    right;reflexivity.
  Qed.

  Lemma Setminus_intro :
    forall (A B:Ensemble U) (x:U),
      In U A x -> ~ In U B x -> In U (Setminus U A B) x.
  Proof.
    intros A B x ha hb.
    red.
    red.
    split;assumption.
  Qed.

  Lemma Strict_Included_intro :
    forall X Y:Ensemble U, Included U X Y /\ X <> Y -> Strict_Included U X Y.
  Proof.
    intros X Y h.
    red.
    assumption.
  Qed.

  Lemma Strict_Included_strict : forall X:Ensemble U, ~ Strict_Included U X X.
  Proof.
    intros X.
    red.
    intro h.
    red in h.
    destruct h as [ _ hneq ].
    red in hneq.
    apply hneq.
    reflexivity.
  Qed.

End Ensembles_facts.

#[global]
Hint Resolve Singleton_inv Singleton_intro Add_intro1 Add_intro2
  Intersection_inv Couple_inv Setminus_intro Strict_Included_intro
  Strict_Included_strict Noone_in_empty Inhabited_not_empty Add_not_Empty
  not_Empty_Add Inhabited_add Included_Empty: sets.
