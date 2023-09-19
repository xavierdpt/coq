(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import DecidableClass.

(** The type [bool] is defined in the prelude as
[[
Inductive bool : Set := true : bool | false : bool
]]
 *)

(** Most of the lemmas in this file are trivial by case analysis *)

Local Ltac Tauto.intuition_solver ::= auto with bool.

Ltac destr_bool :=
 intros; destruct_all bool; simpl in *; trivial; try discriminate.

(** Interpretation of booleans as propositions *)

Definition Is_true (b:bool) :=
  match b with
    | true => True
    | false => False
  end.

(*******************)
(** * Decidability *)
(*******************)

Lemma bool_dec : forall b1 b2 : bool, {b1 = b2} + {b1 <> b2}.
Proof.
  intros x y.
  destruct x, y.
  all: try (left;reflexivity).
  all:right.
  all:red.
  all:inversion 1.
Defined.

(*********************)
(** * Discrimination *)
(*********************)

Lemma diff_true_false : true <> false.
Proof.
red.
intro heq.
set (f:=fun b => match b with true => True | false => False end).
assert (h:=eq_ind).
specialize (h bool).
specialize (h true).
specialize (h f ).
simpl in h.
specialize (h I).
specialize (h false).
simpl in h.
apply h.
assumption.
Qed.
#[global]
Hint Resolve diff_true_false : bool.

Lemma diff_false_true : false <> true.
Proof.
red.
intro heq.
apply diff_true_false.
symmetry.
assumption.
Qed.
#[global]
Hint Resolve diff_false_true : bool.
#[global]
Hint Extern 1 (false <> true) => exact diff_false_true : core.

Lemma eq_true_false_abs : forall b:bool, b = true -> b = false -> False.
Proof.
intro b.
destruct b.
intros _ h. apply diff_true_false. assumption.
intros h _. apply diff_false_true. assumption.
Qed.

Lemma not_true_is_false : forall b:bool, b <> true -> b = false.
Proof.
intro b.
destruct b.
intro h. exfalso. red in h. apply h. reflexivity.
intros _. reflexivity.
Qed.

Lemma not_false_is_true : forall b:bool, b <> false -> b = true.
Proof.
intro b. destruct b.
intros _. reflexivity.
intro h. red in h. exfalso. apply h. reflexivity.
Qed.

Lemma not_true_iff_false : forall b, b <> true <-> b = false.
Proof.
intro b. destruct b.
all:split.
all:intro h.
red in h. exfalso. apply h. reflexivity.
red. intros _. apply diff_true_false. assumption.
reflexivity.
exact diff_false_true.
Qed.

Lemma not_false_iff_true : forall b, b <> false <-> b = true.
Proof.
intro b. destruct b.
all:split.
all:intro h.
reflexivity.
exact diff_true_false.
exfalso. red in h. apply h. reflexivity.
red. intros _. apply diff_false_true. assumption.
Qed.

(************************)
(** * Order on booleans *)
(************************)

#[ local ] Definition le (b1 b2:bool) :=
  match b1 with
    | true => b2 = true
    | false => True
  end.
#[global]
Hint Unfold le: bool.

Lemma le_implb : forall b1 b2, le b1 b2 <-> implb b1 b2 = true.
Proof.
intros b1 b2.
destruct b1, b2.
all:simpl.
all:split.
all:intro h.
all:try exact I.
all:try reflexivity.
all:try assumption.
Qed.

#[ local ] Definition lt (b1 b2:bool) :=
  match b1 with
    | true => False
    | false => b2 = true
  end.
#[global]
Hint Unfold lt: bool.

#[ local ] Definition compare (b1 b2 : bool) :=
  match b1, b2 with
   | false, true => Lt
   | true, false => Gt
   | _, _ => Eq
  end.

Lemma compare_spec : forall b1 b2,
  CompareSpec (b1 = b2) (lt b1 b2) (lt b2 b1) (compare b1 b2).
Proof.
intros b1 b2.
destruct b1, b2.
all:simpl.
apply CompEq. reflexivity.
apply CompGt. reflexivity.
apply CompLt. reflexivity.
apply CompEq. reflexivity.
Qed.


(***************)
(** * Equality *)
(***************)

Definition eqb (b1 b2:bool) : bool :=
  match b1, b2 with
    | true, true => true
    | true, false => false
    | false, true => false
    | false, false => true
  end.

Register eqb as core.bool.eqb.

Lemma eqb_subst :
  forall (P:bool -> Prop) (b1 b2:bool), eqb b1 b2 = true -> P b1 -> P b2.
Proof.
intros P b1 b2.
destruct b1, b2.
all:simpl.
all:intros heq h.
all:try assumption.
all:try exfalso.
apply diff_false_true. assumption.
apply diff_false_true. assumption.
Qed.

Lemma eqb_reflx : forall b:bool, eqb b b = true.
Proof.
intro b.
destruct b.
all:simpl.
all:reflexivity.
Qed.

Lemma eqb_prop : forall a b:bool, eqb a b = true -> a = b.
Proof.
intros a b.
destruct a, b.
all:simpl.
all:intro h.
all:try reflexivity.
symmetry. assumption.
assumption.
Qed.

Lemma eqb_true_iff : forall a b:bool, eqb a b = true <-> a = b.
Proof.
intros a b.
destruct a, b.
all:simpl.
all:split.
all:intro h.
all:try reflexivity.
all:try assumption.
all:symmetry.
all:try assumption.
Qed.

#[global]
Instance Decidable_eq_bool : forall (x y : bool), Decidable (eq x y) := {
  Decidable_spec := eqb_true_iff x y
}.

Lemma eqb_false_iff : forall a b:bool, eqb a b = false <-> a <> b.
Proof.
intros a b.
destruct a, b.
all:simpl.
all:split.
all:intro h.
exfalso. apply diff_true_false. assumption.
exfalso. red in h. apply h. reflexivity.
exact diff_true_false.
reflexivity.
exact diff_false_true.
reflexivity.
exfalso. apply diff_true_false. assumption.
exfalso. red in h. apply h. reflexivity.
Qed.

(**********************************)
(** * A synonym of [if] on [bool] *)
(**********************************)

Definition ifb (b1 b2 b3:bool) : bool :=
  match b1 with
    | true => b2
    | false => b3
  end.

Open Scope bool_scope.

(*********************)
(** * De Morgan laws *)
(*********************)

Lemma negb_orb : forall b1 b2:bool, negb (b1 || b2) = negb b1 && negb b2.
Proof.
intros b1 b2.
destruct b1, b2.
all:simpl.
all:reflexivity.
Qed.

Lemma negb_andb : forall b1 b2:bool, negb (b1 && b2) = negb b1 || negb b2.
Proof.
intros a b.
destruct a, b.
all:simpl.
all:reflexivity.
Qed.

(***************************)
(** * Properties of [negb] *)
(***************************)

Lemma negb_involutive : forall b:bool, negb (negb b) = b.
Proof.
intro b.
destruct b.
all:simpl.
all:reflexivity.
Qed.

Lemma negb_involutive_reverse : forall b:bool, b = negb (negb b).
Proof.
intro b.
destruct b.
all:simpl.
all:reflexivity.
Qed.

Notation negb_elim := negb_involutive (only parsing).
Notation negb_intro := negb_involutive_reverse (only parsing).

Lemma negb_sym : forall b b':bool, b' = negb b -> b = negb b'.
Proof.
intros a b.
destruct a, b.
all:simpl.
all:intro h.
all:try reflexivity.
all:try assumption.
Qed.

Lemma no_fixpoint_negb : forall b:bool, negb b <> b.
Proof.
intro b.
destruct b.
all:simpl.
exact diff_false_true.
exact diff_true_false.
Qed.

Lemma eqb_negb1 : forall b:bool, eqb (negb b) b = false.
Proof.
intro b.
destruct b.
all:simpl.
all:reflexivity.
Qed.

Lemma eqb_negb2 : forall b:bool, eqb b (negb b) = false.
Proof.
intro b.
destruct b.
all:simpl.
all:reflexivity.
Qed.

Lemma if_negb :
  forall (A:Type) (b:bool) (x y:A),
    (if negb b then x else y) = (if b then y else x).
Proof.
intro A.
intro b.
destruct b.
all:intros x y.
all:simpl.
all:reflexivity.
Qed.

Lemma negb_true_iff : forall b, negb b = true <-> b = false.
Proof.
intro b.
destruct b.
all:simpl.
all:split.
all:intro h.
all:try reflexivity.
all:symmetry.
all:try assumption.
Qed.

Lemma negb_false_iff : forall b, negb b = false <-> b = true.
Proof.
intro b.
destruct b.
all:simpl.
all:split.
all:intro h.
all:try reflexivity.
all:symmetry.
all:try assumption.
Qed.


(**************************)
(** * Properties of [orb] *)
(**************************)

Lemma orb_true_iff :
  forall b1 b2, b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
intros a b.
destruct a, b.
all:simpl.
all:split.
all:intro h.
all:try reflexivity.
right. assumption.
left. assumption.
right. assumption.
left. assumption.
destruct h as [ h | h ].
assumption. assumption.
Qed.

Lemma orb_false_iff :
  forall b1 b2, b1 || b2 = false <-> b1 = false /\ b2 = false.
Proof.
intros a b.
destruct a, b.
all:simpl.
all:split.
all:intro h.
all:try split.
all:try reflexivity.
all:try assumption.
all:try destruct h.
all:try assumption.
Qed.

Lemma orb_true_elim :
  forall b1 b2:bool, b1 || b2 = true -> {b1 = true} + {b2 = true}.
Proof.
intros a b.
destruct a, b.
all:simpl.
all:intro h.
left. assumption.
left. assumption.
right. assumption.
left. assumption.
Defined.

Lemma orb_prop : forall a b:bool, a || b = true -> a = true \/ b = true.
Proof.
intros a b.
destruct a, b.
all:simpl.
all:intro h.
all:try (left;reflexivity).
all:try (right;reflexivity).
left. assumption.
Qed.

Lemma orb_true_intro :
  forall b1 b2:bool, b1 = true \/ b2 = true -> b1 || b2 = true.
Proof.
intros a b.
destruct a, b.
all:simpl.
all:intros [ h | h ].
all:try reflexivity.
all:try assumption.
Qed.
#[global]
Hint Resolve orb_true_intro: bool.

Lemma orb_false_intro :
  forall b1 b2:bool, b1 = false -> b2 = false -> b1 || b2 = false.
Proof.
intros a b.
destruct a, b.
all:simpl.
all:intros ha hb.
all:try reflexivity.
all:try assumption.
Qed.
#[global]
Hint Resolve orb_false_intro: bool.

Lemma orb_false_elim :
  forall b1 b2:bool, b1 || b2 = false -> b1 = false /\ b2 = false.
Proof.
intros a b.
destruct a, b.
all:simpl.
all:intro h.
all:split.
all:try reflexivity.
all:try assumption.
Qed.

Lemma orb_diag : forall b, b || b = b.
Proof.
intro b.
destruct b.
all:simpl.
all:reflexivity.
Qed.

(** [true] is a zero for [orb] *)

Lemma orb_true_r : forall b:bool, b || true = true.
Proof.
intro b.
destruct b.
all:simpl.
all:reflexivity.
Qed.
#[global]
Hint Resolve orb_true_r: bool.

Lemma orb_true_l : forall b:bool, true || b = true.
Proof.
intro b.
destruct b.
all:simpl.
all:reflexivity.
Qed.

Notation orb_b_true := orb_true_r (only parsing).
Notation orb_true_b := orb_true_l (only parsing).

(** [false] is neutral for [orb] *)

Lemma orb_false_r : forall b:bool, b || false = b.
Proof.
intro b.
destruct b.
all:simpl.
all:reflexivity.
Qed.
#[global]
Hint Resolve orb_false_r: bool.

Lemma orb_false_l : forall b:bool, false || b = b.
Proof.
intro b.
destruct b.
all:simpl.
all:reflexivity.
Qed.
#[global]
Hint Resolve orb_false_l: bool.

Notation orb_b_false := orb_false_r (only parsing).
Notation orb_false_b := orb_false_l (only parsing).

(** Complementation *)

Lemma orb_negb_r : forall b:bool, b || negb b = true.
Proof.
intro b.
destruct b.
all:simpl.
all:reflexivity.
Qed.
#[global]
Hint Resolve orb_negb_r: bool.

Lemma orb_negb_l : forall b:bool, negb b || b = true.
Proof.
intro b.
destruct b.
all:simpl.
all:reflexivity.
Qed.

Notation orb_neg_b := orb_negb_r (only parsing).

(** Commutativity *)

Lemma orb_comm : forall b1 b2:bool, b1 || b2 = b2 || b1.
Proof.
intros a b.
destruct a, b.
all:simpl.
all:reflexivity.
Qed.

(** Associativity *)

Lemma orb_assoc : forall b1 b2 b3:bool, b1 || (b2 || b3) = b1 || b2 || b3.
Proof.
intros a b c.
destruct a, b, c.
all:simpl.
all:reflexivity.
Qed.
#[global]
Hint Resolve orb_comm orb_assoc: bool.

(***************************)
(** * Properties of [andb] *)
(***************************)

Lemma andb_true_iff :
  forall b1 b2:bool, b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
intros a b.
destruct a, b.
all:simpl.
all:split.
all:try intros [ha hb].
all:try intro h.
all:try split.
all:try reflexivity.
all:try assumption.
Qed.

Lemma andb_false_iff :
  forall b1 b2:bool, b1 && b2 = false <-> b1 = false \/ b2 = false.
Proof.
intros a b.
destruct a, b.
all:simpl.
all:split.
all:try intros [ h | h ].
all:try intro h.
all:try reflexivity.
all:try assumption.
all:try (left;assumption).
all:try (right;assumption).
Qed.

Lemma andb_true_eq :
  forall a b:bool, true = a && b -> true = a /\ true = b.
Proof.
intros a b.
destruct a, b.
all:simpl.
all: intro h.
all:split.
all:try reflexivity.
all:try assumption.
Defined.

Lemma andb_false_intro1 : forall b1 b2:bool, b1 = false -> b1 && b2 = false.
Proof.
intros a b.
destruct a, b.
all:simpl.
all:intro h.
all:try reflexivity.
all:try assumption.
Qed.

Lemma andb_false_intro2 : forall b1 b2:bool, b2 = false -> b1 && b2 = false.
Proof.
intros a b.
destruct a, b.
all:simpl.
all:intro h.
all:try reflexivity.
all:assumption.
Qed.

(** [false] is a zero for [andb] *)

Lemma andb_false_r : forall b:bool, b && false = false.
Proof.
intro b.
destruct b.
all:simpl.
all:reflexivity.
Qed.

Lemma andb_false_l : forall b:bool, false && b = false.
Proof.
intro b.
destruct b.
all:simpl.
all:reflexivity.
Qed.

Notation andb_b_false := andb_false_r (only parsing).
Notation andb_false_b := andb_false_l (only parsing).

Lemma andb_diag : forall b, b && b = b.
Proof.
intro b.
destruct b.
all:simpl.
all:reflexivity.
Qed.

(** [true] is neutral for [andb] *)

Lemma andb_true_r : forall b:bool, b && true = b.
Proof.
intro b.
destruct b.
all:simpl.
all:reflexivity.
Qed.

Lemma andb_true_l : forall b:bool, true && b = b.
Proof.
intro b.
destruct b.
all:simpl.
all:reflexivity.
Qed.

Notation andb_b_true := andb_true_r (only parsing).
Notation andb_true_b := andb_true_l (only parsing).

Lemma andb_false_elim :
  forall b1 b2:bool, b1 && b2 = false -> {b1 = false} + {b2 = false}.
Proof.
intros a b.
destruct a, b.
all:simpl.
all:intro h.
all:try (left;reflexivity).
all:try (right;reflexivity).
left;assumption.
Defined.
#[global]
Hint Resolve andb_false_elim: bool.

(** Complementation *)

Lemma andb_negb_r : forall b:bool, b && negb b = false.
Proof.
intro b.
destruct b.
all:simpl.
all:reflexivity.
Qed.
#[global]
Hint Resolve andb_negb_r: bool.

Lemma andb_negb_l : forall b:bool, negb b && b = false.
Proof.
intro b.
destruct b.
all:simpl.
all:reflexivity.
Qed.

Notation andb_neg_b := andb_negb_r (only parsing).

(** Commutativity *)

Lemma andb_comm : forall b1 b2:bool, b1 && b2 = b2 && b1.
Proof.
intros a b.
destruct a, b.
all:simpl.
all:reflexivity.
Qed.

(** Associativity *)

Lemma andb_assoc : forall b1 b2 b3:bool, b1 && (b2 && b3) = b1 && b2 && b3.
Proof.
intros a b c.
destruct a, b, c.
all:simpl.
all:reflexivity.
Qed.

#[global]
Hint Resolve andb_comm andb_assoc: bool.

(*****************************************)
(** * Properties mixing [andb] and [orb] *)
(*****************************************)

(** Distributivity *)

Lemma andb_orb_distrib_r :
  forall b1 b2 b3:bool, b1 && (b2 || b3) = b1 && b2 || b1 && b3.
Proof.
intros a b c.
destruct a, b, c.
all:simpl.
all:reflexivity.
Qed.

Lemma andb_orb_distrib_l :
 forall b1 b2 b3:bool, (b1 || b2) && b3 = b1 && b3 || b2 && b3.
Proof.
intros a b c.
destruct a, b, c.
all:simpl.
all:reflexivity.
Qed.

Lemma orb_andb_distrib_r :
  forall b1 b2 b3:bool, b1 || b2 && b3 = (b1 || b2) && (b1 || b3).
Proof.
intros a b c.
destruct a, b, c.
all:simpl.
all:reflexivity.
Qed.

Lemma orb_andb_distrib_l :
  forall b1 b2 b3:bool, b1 && b2 || b3 = (b1 || b3) && (b2 || b3).
Proof.
intros a b c.
destruct a, b, c.
all:simpl.
all:reflexivity.
Qed.

(* Compatibility *)
Notation demorgan1 := andb_orb_distrib_r (only parsing).
Notation demorgan2 := andb_orb_distrib_l (only parsing).
Notation demorgan3 := orb_andb_distrib_r (only parsing).
Notation demorgan4 := orb_andb_distrib_l (only parsing).

(** Absorption *)

Lemma absorption_andb : forall b1 b2:bool, b1 && (b1 || b2) = b1.
Proof.
intros a b.
destruct a, b.
all:simpl.
all:reflexivity.
Qed.

Lemma absorption_orb : forall b1 b2:bool, b1 || b1 && b2 = b1.
Proof.
intros a b.
destruct a, b.
all:simpl.
all:reflexivity.
Qed.

(* begin hide *)
(* Compatibility *)
Notation absoption_andb := absorption_andb (only parsing).
Notation absoption_orb := absorption_orb (only parsing).
(* end hide *)

(****************************)
(** * Properties of [implb] *)
(****************************)

Lemma implb_true_iff : forall b1 b2:bool, implb b1 b2 = true <-> (b1 = true -> b2 = true).
Proof.
intros a b.
destruct a, b.
all:simpl.
all:split.
all:try intros ha hb.
all:try intro h.
all:try reflexivity.
all:try assumption.
apply h. reflexivity.
Qed.

Lemma implb_false_iff : forall b1 b2:bool, implb b1 b2 = false <-> (b1 = true /\ b2 = false).
Proof.
intros a b.
destruct a, b.
all:simpl.
all:split.
all:try intros [ha hb].
all:try intro h.
all:try split.
all:try reflexivity.
all:try assumption.
all:symmetry.
all:try assumption.
Qed.

Lemma implb_orb : forall b1 b2:bool, implb b1 b2 = negb b1 || b2.
Proof.
intros a b.
destruct a, b.
all:simpl.
all:reflexivity.
Qed.

Lemma implb_negb_orb : forall b1 b2:bool, implb (negb b1) b2 = b1 || b2.
Proof.
intros a b.
destruct a, b.
all:simpl.
all:reflexivity.
Qed.

Lemma implb_true_r : forall b:bool, implb b true = true.
Proof.
intro b.
destruct b.
all:simpl.
all:reflexivity.
Qed.

Lemma implb_false_r : forall b:bool, implb b false = negb b.
Proof.
intro b.
destruct b.
all:simpl.
all:reflexivity.
Qed.

Lemma implb_true_l : forall b:bool, implb true b = b.
Proof.
intro b.
destruct b.
all:simpl.
all:reflexivity.
Qed.

Lemma implb_false_l : forall b:bool, implb false b = true.
Proof.
intro b.
destruct b.
all:simpl.
all:reflexivity.
Qed.

Lemma implb_same : forall b:bool, implb b b = true.
Proof.
intro b.
destruct b.
all:simpl.
all:reflexivity.
Qed.

Lemma implb_contrapositive : forall b1 b2:bool, implb (negb b1) (negb b2) = implb b2 b1.
Proof.
intros a b.
destruct a, b.
all:simpl.
all:reflexivity.
Qed.

Lemma implb_negb : forall b1 b2:bool, implb (negb b1) b2 = implb (negb b2) b1.
Proof.
intros a b.
destruct a, b.
all:simpl.
all:reflexivity.
Qed.

Lemma implb_curry : forall b1 b2 b3:bool, implb (b1 && b2) b3 = implb b1 (implb b2 b3).
Proof.
intros a b c.
destruct a, b, c.
all:simpl.
all:reflexivity.
Qed.

Lemma implb_andb_distrib_r : forall b1 b2 b3:bool, implb b1 (b2 && b3) = implb b1 b2 && implb b1 b3.
Proof.
intros a b c.
destruct a, b, c.
all:simpl.
all:reflexivity.
Qed.

Lemma implb_orb_distrib_r : forall b1 b2 b3:bool, implb b1 (b2 || b3) = implb b1 b2 || implb b1 b3.
Proof.
intros a b c.
destruct a, b, c.
all:simpl.
all:reflexivity.
Qed.

Lemma implb_orb_distrib_l : forall b1 b2 b3:bool, implb (b1 || b2) b3 = implb b1 b3 && implb b2 b3.
Proof.
intros a b c.
destruct a, b, c.
all:simpl.
all:reflexivity.
Qed.

(***************************)
(** * Properties of [xorb] *)
(***************************)

(** [false] is neutral for [xorb] *)

Lemma xorb_false_r : forall b:bool, xorb b false = b.
Proof.
intros b.
destruct b.
all:simpl.
all:reflexivity.
Qed.

Lemma xorb_false_l : forall b:bool, xorb false b = b.
Proof.
intros b.
destruct b.
all:simpl.
all:reflexivity.
Qed.

Notation xorb_false := xorb_false_r (only parsing).
Notation false_xorb := xorb_false_l (only parsing).

(** [true] is "complementing" for [xorb] *)

Lemma xorb_true_r : forall b:bool, xorb b true = negb b.
Proof.
intros b.
destruct b.
all:simpl.
all:reflexivity.
Qed.

Lemma xorb_true_l : forall b:bool, xorb true b = negb b.
Proof.
intros b.
destruct b.
all:simpl.
all:reflexivity.
Qed.

Notation xorb_true := xorb_true_r (only parsing).
Notation true_xorb := xorb_true_l (only parsing).

(** Nilpotency (alternatively: identity is a inverse for [xorb]) *)

Lemma xorb_nilpotent : forall b:bool, xorb b b = false.
Proof.
intros b.
destruct b.
all:simpl.
all:reflexivity.
Qed.

(** Commutativity *)

Lemma xorb_comm : forall b b':bool, xorb b b' = xorb b' b.
Proof.
intros a b.
destruct a, b.
all:simpl.
all:reflexivity.
Qed.

(** Associativity *)

Lemma xorb_assoc_reverse :
  forall b b' b'':bool, xorb (xorb b b') b'' = xorb b (xorb b' b'').
Proof.
intros a b c.
destruct a, b, c.
all:simpl.
all:reflexivity.
Qed.

Notation xorb_assoc := xorb_assoc_reverse (only parsing). (* Compatibility *)

Lemma xorb_eq : forall b b':bool, xorb b b' = false -> b = b'.
Proof.
intros a b.
destruct a, b.
all:simpl.
all:intro h.
all:try reflexivity.
all:try assumption.
symmetry. assumption.
Qed.

Lemma xorb_move_l_r_1 :
  forall b b' b'':bool, xorb b b' = b'' -> b' = xorb b b''.
Proof.
intros a b c.
destruct a, b, c.
all:simpl.
all:intro h.
all:try reflexivity.
all:try assumption.
all:symmetry.
all:assumption.
Qed.

Lemma xorb_move_l_r_2 :
  forall b b' b'':bool, xorb b b' = b'' -> b = xorb b'' b'.
Proof.
intros a b c.
destruct a, b, c.
all:simpl.
all:intro h.
all:try reflexivity.
all:try assumption.
all:symmetry.
all:assumption.
Qed.

Lemma xorb_move_r_l_1 :
  forall b b' b'':bool, b = xorb b' b'' -> xorb b' b = b''.
Proof.
intros a b c.
destruct a, b, c.
all:simpl.
all:intro h.
all:try reflexivity.
all:try assumption.
all:symmetry.
all:assumption.
Qed.

Lemma xorb_move_r_l_2 :
  forall b b' b'':bool, b = xorb b' b'' -> xorb b b'' = b'.
Proof.
intros a b c.
destruct a, b, c.
all:simpl.
all:intro h.
all:try reflexivity.
all:try assumption.
all:symmetry.
all:assumption.
Qed.

Lemma negb_xorb a b : negb (xorb a b) = Bool.eqb a b.
Proof.
destruct a, b.
all:simpl.
all:reflexivity.
Qed.

Lemma negb_xorb_l : forall b b', negb (xorb b b') = xorb (negb b) b'.
Proof.
intros a b.
destruct a, b.
all:simpl.
all:reflexivity.
Qed.

Lemma negb_xorb_r : forall b b', negb (xorb b b') = xorb b (negb b').
Proof.
intros a b.
destruct a, b.
all:simpl.
all:reflexivity.
Qed.

Lemma xorb_negb_negb : forall b b', xorb (negb b) (negb b') = xorb b b'.
Proof.
intros a b.
destruct a, b.
all:simpl.
all:reflexivity.
Qed.

(** Lemmas about the [b = true] embedding of [bool] to [Prop] *)

Lemma eq_iff_eq_true : forall b1 b2, b1 = b2 <-> (b1 = true <-> b2 = true).
Proof.
intros a b.
destruct a, b.
all:split.
all:try intros [ hl hr ].
all:try intro h.
all:try split.
all:try intro h'.
all:try reflexivity.
all:try assumption.
all:symmetry.
all:try assumption.
apply hl. reflexivity.
symmetry. apply hr. reflexivity.
Qed.

Lemma eq_true_iff_eq : forall b1 b2, (b1 = true <-> b2 = true) -> b1 = b2.
Proof.
intros a b.
destruct a, b.
all:intros [hl hr].
all:try reflexivity.
symmetry. apply hl. reflexivity.
apply hr. reflexivity.
Qed.

Notation bool_1 := eq_true_iff_eq (only parsing). (* Compatibility *)

Lemma eq_true_negb_classical : forall b:bool, negb b <> true -> b = true.
Proof.
intro b.
destruct b.
all:simpl.
all:intro h.
all:red in h.
reflexivity.
exfalso. apply h. reflexivity.
Qed.

Notation bool_3 := eq_true_negb_classical (only parsing). (* Compatibility *)

Lemma eq_true_not_negb : forall b:bool, b <> true -> negb b = true.
Proof.
destruct b.
all:simpl.
all:intro h.
all:red in h.
exfalso. apply h. reflexivity.
reflexivity.
Qed.

Notation bool_6 := eq_true_not_negb (only parsing). (* Compatibility *)

#[global]
Hint Resolve eq_true_not_negb : bool.

(* An interesting lemma for auto but too strong to keep compatibility *)

Lemma absurd_eq_bool : forall b b':bool, False -> b = b'.
Proof.
intros a b.
destruct 1.
Qed.

(* A more specific one that preserves compatibility with old hint bool_3 *)

Lemma absurd_eq_true : forall b, False -> b = true.
Proof.
intro b.
destruct 1.
Qed.
#[global]
Hint Resolve absurd_eq_true : core.

(* A specific instance of eq_trans that preserves compatibility with
   old hint bool_2 *)

Lemma trans_eq_bool : forall x y z:bool, x = y -> y = z -> x = z.
Proof.
intros a b c.
destruct a, b, c.
all:intros ha hb.
all:try reflexivity.
all:try assumption.
Qed.
#[global]
Hint Resolve trans_eq_bool : core.

(***************************************)
(** * Reflection of [bool] into [Prop] *)
(***************************************)

(** [Is_true] and equality *)

#[global]
Hint Unfold Is_true: bool.

Lemma Is_true_eq_true : forall x:bool, Is_true x -> x = true.
Proof.
intros b.
destruct b.
all:simpl.
intros _. reflexivity.
destruct 1.
Qed.

Lemma Is_true_eq_left : forall x:bool, x = true -> Is_true x.
Proof.
intros b.
destruct b.
all:simpl.
intros _. trivial.
exact diff_false_true.
Qed.

Lemma Is_true_eq_right : forall x:bool, true = x -> Is_true x.
Proof.
intros b.
destruct b.
all:simpl.
intros _. trivial.
exact diff_true_false.
Qed.

Notation Is_true_eq_true2 := Is_true_eq_right (only parsing).

#[global]
Hint Immediate Is_true_eq_right Is_true_eq_left: bool.

Lemma eqb_refl : forall x:bool, Is_true (eqb x x).
Proof.
intro b. destruct b.
all:simpl. all:trivial.
Qed.

Lemma eqb_eq : forall x y:bool, Is_true (eqb x y) -> x = y.
Proof.
intros a b.
destruct a, b.
all:simpl.
all:destruct 1.
all:reflexivity.
Qed.

(** [Is_true] and connectives *)

Lemma orb_prop_elim :
  forall a b:bool, Is_true (a || b) -> Is_true a \/ Is_true b.
Proof.
intros a b.
destruct a, b.
all:simpl.
all:destruct 1.
all:try (left;exact I).
right. trivial.
Qed.

Notation orb_prop2 := orb_prop_elim (only parsing).

Lemma orb_prop_intro :
  forall a b:bool, Is_true a \/ Is_true b -> Is_true (a || b).
Proof.
intros a b.
destruct a, b.
all:simpl.
all:intros [ h | h ].
all:try assumption.
all:trivial.
Qed.

Lemma andb_prop_intro :
  forall b1 b2:bool, Is_true b1 /\ Is_true b2 -> Is_true (b1 && b2).
Proof.
intros a b.
destruct a, b.
all:simpl.
all:intros [ ha hb ].
all:try assumption.
Qed.
#[global]
Hint Resolve andb_prop_intro: bool.

Notation andb_true_intro2 :=
  (fun b1 b2 H1 H2 => andb_prop_intro b1 b2 (conj H1 H2))
  (only parsing).

Lemma andb_prop_elim :
  forall a b:bool, Is_true (a && b) -> Is_true a /\ Is_true b.
Proof.
intros a b.
destruct a, b.
all:simpl.
all:destruct 1.
split.
all:trivial.
Qed.
#[global]
Hint Resolve andb_prop_elim: bool.

Notation andb_prop2 := andb_prop_elim (only parsing).

Lemma eq_bool_prop_intro :
  forall b1 b2, (Is_true b1 <-> Is_true b2) -> b1 = b2.
Proof.
intros a b.
destruct a, b.
all:simpl.
all:intros [ hl hr ].
all:try reflexivity.
all:exfalso.
apply hl. trivial.
apply hr. trivial.
Qed.

Lemma eq_bool_prop_elim : forall b1 b2, b1 = b2 -> (Is_true b1 <-> Is_true b2).
Proof.
intros a b.
destruct a, b.
all:simpl.
all:intro h.
all:split.
all:destruct 1.
all:try trivial.
apply diff_true_false. assumption.
apply diff_false_true. assumption.
Qed.

Lemma negb_prop_elim : forall b, Is_true (negb b) -> ~ Is_true b.
Proof.
intros b.
destruct b.
all:simpl.
all:destruct 1.
red. intro h. assumption.
Qed.

Lemma negb_prop_intro : forall b, ~ Is_true b -> Is_true (negb b).
Proof.
intro b.
destruct b.
all:simpl.
all:unfold not.
all:intro h.
2:trivial.
apply h. trivial.
Qed.

Lemma negb_prop_classical : forall b, ~ Is_true (negb b) -> Is_true b.
Proof.
intro b.
destruct b.
all:simpl.
all:unfold not.
all:intro h.
trivial.
apply h. trivial.
Qed.

Lemma negb_prop_involutive : forall b, Is_true b -> ~ Is_true (negb b).
Proof.
intro b.
destruct b.
all:simpl.
all:unfold not.
all:destruct 1.
destruct 1.
Qed.

(** Rewrite rules about andb, orb and if (used in romega) *)

Lemma andb_if : forall (A:Type)(a a':A)(b b' : bool),
  (if b && b' then a else a') =
  (if b then if b' then a else a' else a').
Proof.
intros A x y b c.
destruct b, c.
all:simpl.
all:reflexivity.
Qed.

Lemma negb_if : forall (A:Type)(a a':A)(b:bool),
 (if negb b then a else a') =
 (if b then a' else a).
Proof.
intros A x y b.
destruct b.
all:simpl.
all:reflexivity.
Qed.

(***********************************************)
(** * Alternative versions of [andb] and [orb]
    with lazy behavior (for vm_compute)        *)
(***********************************************)

Declare Scope lazy_bool_scope.

Notation "a &&& b" := (if a then b else false)
 (at level 40, left associativity) : lazy_bool_scope.
Notation "a ||| b" := (if a then true else b)
 (at level 50, left associativity) : lazy_bool_scope.

Local Open Scope lazy_bool_scope.

Lemma andb_lazy_alt : forall a b : bool, a && b = a &&& b.
Proof.
intros a b.
destruct a, b.
all:simpl.
all:reflexivity.
Qed.

Lemma orb_lazy_alt : forall a b : bool, a || b = a ||| b.
Proof.
intros a b.
destruct a, b.
all:simpl.
all:reflexivity.
Qed.

(************************************************)
(** * Reflect: a specialized inductive type for
    relating propositions and booleans,
    as popularized by the Ssreflect library.    *)
(************************************************)

Inductive reflect (P : Prop) : bool -> Set :=
  | ReflectT : P -> reflect P true
  | ReflectF : ~ P -> reflect P false.
#[global]
Hint Constructors reflect : bool.

(** Interest: a case on a reflect lemma or hyp performs clever
    unification, and leave the goal in a convenient shape
    (a bit like case_eq). *)

(** Relation with iff : *)

Lemma reflect_iff : forall P b, reflect P b -> (P<->b=true).
Proof.
intros P b.
intro hr.
split.
intro hp.
destruct hr. reflexivity. exfalso. apply n. assumption.
intro heq. destruct hr. assumption. exfalso. apply diff_false_true. assumption.
Qed.

Lemma iff_reflect : forall P b, (P<->b=true) -> reflect P b.
Proof.
intro P.
intro b.
intros [ hl hr ].
destruct b.
constructor. apply hr. reflexivity.
constructor. red. intro hp. apply diff_false_true. apply hl. assumption.
Defined.

(** It would be nice to join [reflect_iff] and [iff_reflect]
    in a unique [iff] statement, but this isn't allowed since
    [iff] is in Prop. *)

(** Reflect implies decidability of the proposition *)

Lemma reflect_dec : forall P b, reflect P b -> {P}+{~P}.
Proof.
intros P b.
intro hr.
destruct hr.
left. assumption.
right. assumption.
Defined.

(** Reciprocally, from a decidability, we could state a
    [reflect] as soon as we have a [bool_of_sumbool]. *)

(** For instance, we could state the correctness of [Bool.eqb] via [reflect]: *)

Lemma eqb_spec (b b' : bool) : reflect (b = b') (eqb b b').
Proof.
destruct b, b'.
all:simpl.
all:constructor.
all:try reflexivity.
exact diff_true_false.
exact diff_false_true.
Defined.

(** Notations *)
Module BoolNotations.
Infix "<=" := le : bool_scope.
Infix "<" := lt : bool_scope.
Infix "?=" := compare (at level 70) : bool_scope.
Infix "=?" := eqb (at level 70) : bool_scope.
End BoolNotations.
