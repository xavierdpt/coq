(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Tactics related to (dependent) equality and proof irrelevance. *)

Require Export ProofIrrelevance.
Require Export JMeq.

Require Import Coq.Program.Tactics.

Local Notation "'Π'  x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity) : type_scope.

Ltac is_ground_goal := 
  match goal with
    |- ?T => is_ground T
  end.

(** Try to find a contradiction. *)

Hint Extern 10 => is_ground_goal ; progress exfalso : exfalso.

(** We will use the [block] definition to separate the goal from the 
   equalities generated by the tactic. *)

Definition block {A : Type} (a : A) := a.

Ltac block_goal := match goal with [ |- ?T ] => change (block T) end.
Ltac unblock_goal := unfold block at 1.
Ltac unblock_all := unfold block in *.

(** Notation for heterogenous equality. *)

Notation " x ~= y " := (@JMeq _ x _ y) (at level 70, no associativity).

(** Notation for the single element of [x = x] and [x ~= x]. *)

Implicit Arguments eq_refl [[A] [x]] [A].
Implicit Arguments JMeq_refl [[A] [x]] [A].

(** Do something on an heterogeneous equality appearing in the context. *)

Ltac on_JMeq tac :=
  match goal with
    | [ H : @JMeq ?x ?X ?y ?Y |- _ ] => tac H
  end.

(** Try to apply [JMeq_eq] to get back a regular equality when the two types are equal. *)

Ltac simpl_one_JMeq :=
  on_JMeq ltac:(fun H => apply JMeq_eq in H).

(** Repeat it for every possible hypothesis. *)

Ltac simpl_JMeq := repeat simpl_one_JMeq.

(** Just simplify an h.eq. without clearing it. *)

Ltac simpl_one_dep_JMeq :=
  on_JMeq
  ltac:(fun H => let H' := fresh "H" in
    assert (H' := JMeq_eq H)).

Require Import Eqdep.

(** Simplify dependent equality using sigmas to equality of the second projections if possible.
   Uses UIP. *)

Ltac simpl_existT :=
  match goal with
    [ H : existT _ ?x _ = existT _ ?x _ |- _ ] =>
    let Hi := fresh H in assert(Hi:=inj_pairT2 _ _ _ _ _ H) ; clear H
  end.

Ltac simpl_existTs := repeat simpl_existT.

(** Tries to eliminate a call to [eq_rect] (the substitution principle) by any means available. *)

Ltac elim_eq_rect :=
  match goal with
    | [ |- ?t ] =>
      match t with
        | context [ @eq_rect _ _ _ _ _ ?p ] =>
          let P := fresh "P" in
            set (P := p); simpl in P ;
	      ((case P ; clear P) || (clearbody P; rewrite (UIP_refl _ _ P); clear P))
        | context [ @eq_rect _ _ _ _ _ ?p _ ] =>
          let P := fresh "P" in
            set (P := p); simpl in P ;
	      ((case P ; clear P) || (clearbody P; rewrite (UIP_refl _ _ P); clear P))
      end
  end.

(** Rewrite using uniqueness of indentity proofs [H = eq_refl]. *)

Ltac simpl_uip :=
  match goal with
    [ H : ?X = ?X |- _ ] => rewrite (UIP_refl _ _ H) in *; clear H
  end.

(** Simplify equalities appearing in the context and goal. *)

Ltac simpl_eq := simpl ; unfold eq_rec_r, eq_rec ; repeat (elim_eq_rect ; simpl) ; repeat (simpl_uip ; simpl).

(** Try to abstract a proof of equality, if no proof of the same equality is present in the context. *)

Ltac abstract_eq_hyp H' p :=
  let ty := type of p in
  let tyred := eval simpl in ty in
    match tyred with
      ?X = ?Y =>
      match goal with
        | [ H : X = Y |- _ ] => fail 1
        | _ => set (H':=p) ; try (change p with H') ; clearbody H' ; simpl in H'
      end
    end.

(** Apply the tactic tac to proofs of equality appearing as coercion arguments.
   Just redefine this tactic (using [Ltac on_coerce_proof tac ::=]) to handle custom coercion operators.
   *)

Ltac on_coerce_proof tac T :=
  match T with
    | context [ eq_rect _ _ _ _ ?p ] => tac p
  end.

Ltac on_coerce_proof_gl tac :=
  match goal with
    [ |- ?T ] => on_coerce_proof tac T
  end.

(** Abstract proofs of equalities of coercions. *)

Ltac abstract_eq_proof := on_coerce_proof_gl ltac:(fun p => let H := fresh "eqH" in abstract_eq_hyp H p).

Ltac abstract_eq_proofs := repeat abstract_eq_proof.

(** Factorize proofs, by using proof irrelevance so that two proofs of the same equality
   in the goal become convertible. *)

Ltac pi_eq_proof_hyp p :=
  let ty := type of p in
  let tyred := eval simpl in ty in
  match tyred with
    ?X = ?Y =>
    match goal with
      | [ H : X = Y |- _ ] =>
        match p with
          | H => fail 2
          | _ => rewrite (proof_irrelevance (X = Y) p H)
        end
      | _ => fail " No hypothesis with same type "
    end
  end.

(** Factorize proofs of equality appearing as coercion arguments. *)

Ltac pi_eq_proof := on_coerce_proof_gl pi_eq_proof_hyp.

Ltac pi_eq_proofs := repeat pi_eq_proof.

(** The two preceding tactics in sequence. *)

Ltac clear_eq_proofs :=
  abstract_eq_proofs ; pi_eq_proofs.

Hint Rewrite <- eq_rect_eq : refl_id.

(** The [refl_id] database should be populated with lemmas of the form
   [coerce_* t eq_refl = t]. *)

Lemma JMeq_eq_refl {A} (x : A) : JMeq_eq (@JMeq_refl _ x) = eq_refl.
Proof. intros. apply proof_irrelevance. Qed.

Lemma UIP_refl_refl : Π A (x : A),
  Eqdep.EqdepTheory.UIP_refl A x eq_refl = eq_refl.
Proof. intros. apply UIP_refl. Qed.

Lemma inj_pairT2_refl : Π A (x : A) (P : A -> Type) (p : P x),
  Eqdep.EqdepTheory.inj_pairT2 A P x p p eq_refl = eq_refl.
Proof. intros. apply UIP_refl. Qed.

Hint Rewrite @JMeq_eq_refl @UIP_refl_refl @inj_pairT2_refl : refl_id.

Ltac rewrite_refl_id := autorewrite with refl_id.

(** Clear the context and goal of equality proofs. *)

Ltac clear_eq_ctx :=
  rewrite_refl_id ; clear_eq_proofs.

(** Reapeated elimination of [eq_rect] applications.
   Abstracting equalities makes it run much faster than an naive implementation. *)

Ltac simpl_eqs :=
  repeat (elim_eq_rect ; simpl ; clear_eq_ctx).

(** Clear unused reflexivity proofs. *)

Ltac clear_refl_eq :=
  match goal with [ H : ?X = ?X |- _ ] => clear H end.
Ltac clear_refl_eqs := repeat clear_refl_eq.

(** Clear unused equality proofs. *)

Ltac clear_eq :=
  match goal with [ H : _ = _ |- _ ] => clear H end.
Ltac clear_eqs := repeat clear_eq.

(** Combine all the tactics to simplify goals containing coercions. *)

Ltac simplify_eqs :=
  simpl ; simpl_eqs ; clear_eq_ctx ; clear_refl_eqs ;
    try subst ; simpl ; repeat simpl_uip ; rewrite_refl_id.

(** A tactic that tries to remove trivial equality guards in induction hypotheses coming
   from [dependent induction]/[generalize_eqs] invocations. *)

Ltac simplify_IH_hyps := repeat
  match goal with
    | [ hyp : context [ block _ ] |- _ ] => specialize_eqs hyp ; unfold block in hyp
  end.

(** We split substitution tactics in the two directions depending on which 
   names we want to keep corresponding to the generalization performed by the
   [generalize_eqs] tactic. *)

Ltac subst_left_no_fail :=
  repeat (match goal with
            [ H : ?X = ?Y |- _ ] => subst X
          end).

Ltac subst_right_no_fail :=
  repeat (match goal with
            [ H : ?X = ?Y |- _ ] => subst Y
          end).

Ltac inject_left H :=
  progress (inversion H ; subst_left_no_fail ; clear_dups) ; clear H.

Ltac inject_right H :=
  progress (inversion H ; subst_right_no_fail ; clear_dups) ; clear H.

Ltac autoinjections_left := repeat autoinjection ltac:inject_left.
Ltac autoinjections_right := repeat autoinjection ltac:inject_right.

Ltac simpl_depind := subst_no_fail ; autoinjections ; try discriminates ; 
  simpl_JMeq ; simpl_existTs ; simplify_IH_hyps.

Ltac simpl_depind_l := subst_left_no_fail ; autoinjections_left ; try discriminates ; 
  simpl_JMeq ; simpl_existTs ; simplify_IH_hyps.

Ltac simpl_depind_r := subst_right_no_fail ; autoinjections_right ; try discriminates ; 
  simpl_JMeq ; simpl_existTs ; simplify_IH_hyps.

Ltac blocked t := block_goal ; t ; unblock_goal.

(** The [DependentEliminationPackage] provides the default dependent elimination principle to
   be used by the [equations] resolver. It is especially useful to register the dependent elimination
   principles for things in [Prop] which are not automatically generated. *)

Class DependentEliminationPackage (A : Type) :=
  { elim_type : Type ; elim : elim_type }.

(** A higher-order tactic to apply a registered eliminator. *)

Ltac elim_tac tac p :=
  let ty := type of p in
  let eliminator := eval simpl in (elim (A:=ty)) in
    tac p eliminator.

(** Specialization to do case analysis or induction.
   Note: the [equations] tactic tries [case] before [elim_case]: there is no need to register
   generated induction principles. *)

Ltac elim_case p := elim_tac ltac:(fun p el => destruct p using el) p.
Ltac elim_ind p := elim_tac ltac:(fun p el => induction p using el) p.

(** Lemmas used by the simplifier, mainly rephrasings of [eq_rect], [eq_ind]. *)

Lemma solution_left : Π A (B : A -> Type) (t : A), B t -> (Π x, x = t -> B x).
Proof. intros; subst. apply X. Defined.

Lemma solution_right : Π A (B : A -> Type) (t : A), B t -> (Π x, t = x -> B x).
Proof. intros; subst; apply X. Defined.

Lemma deletion : Π A B (t : A), B -> (t = t -> B).
Proof. intros; assumption. Defined.

Lemma simplification_heq : Π A B (x y : A), (x = y -> B) -> (JMeq x y -> B).
Proof. intros; apply X; apply (JMeq_eq H). Defined.

Lemma simplification_existT2 : Π A (P : A -> Type) B (p : A) (x y : P p),
  (x = y -> B) -> (existT P p x = existT P p y -> B).
Proof. intros. apply X. apply inj_pair2. exact H. Defined.

Lemma simplification_existT1 : Π A (P : A -> Type) B (p q : A) (x : P p) (y : P q),
  (p = q -> existT P p x = existT P q y -> B) -> (existT P p x = existT P q y -> B).
Proof. intros. injection H. intros ; auto. Defined.
  
Lemma simplification_K : Π A (x : A) (B : x = x -> Type), B eq_refl -> (Π p : x = x, B p).
Proof. intros. rewrite (UIP_refl A). assumption. Defined.

(** This hint database and the following tactic can be used with [autounfold] to 
   unfold everything to [eq_rect]s. *)

Hint Unfold solution_left solution_right deletion simplification_heq
  simplification_existT1 simplification_existT2 simplification_K
  eq_rect_r eq_rec eq_ind : dep_elim.

(** Using these we can make a simplifier that will perform the unification
   steps needed to put the goal in normalised form (provided there are only
   constructor forms). Compare with the lemma 16 of the paper.
   We don't have a [noCycle] procedure yet. *)

Ltac block_equality id :=
  match type of id with
    | @eq ?A ?t ?u => change (block (@eq A t u)) in id
    | _ => idtac
  end.

Ltac revert_blocking_until id := 
  Tactics.on_last_hyp ltac:(fun id' =>
    match id' with
      | id => idtac
      | _ => block_equality id' ; revert id' ; revert_blocking_until id
    end).

Ltac simplify_one_dep_elim_term c :=
  match c with
    | @JMeq _ _ _ _ -> _ => refine (simplification_heq _ _ _ _ _)
    | ?t = ?t -> _ => intros _ || refine (simplification_K _ t _ _)
    | eq (existT _ ?p _) (existT _ ?q _) -> _ =>
      refine (simplification_existT2 _ _ _ _ _ _ _) ||
        match goal with
          | H : p = q |- _ => intro
          | _ => refine (simplification_existT1 _ _ _ _ _ _ _ _)
        end
    | ?x = ?y -> _ => (* variables case *)
      (let hyp := fresh in intros hyp ;
        move hyp before x ; revert_blocking_until hyp ; generalize dependent x ;
          refine (solution_left _ _ _ _)(*  ; intros until 0 *)) ||
      (let hyp := fresh in intros hyp ;
        move hyp before y ; revert_blocking_until hyp ; generalize dependent y ;
          refine (solution_right _ _ _ _)(*  ; intros until 0 *))
    | ?f ?x = ?g ?y -> _ => let H := fresh in progress (intros H ; injection H ; clear H)
    | ?t = ?u -> _ => let hyp := fresh in
      intros hyp ; exfalso ; discriminate
    | ?x = ?y -> _ => let hyp := fresh in
      intros hyp ; (try (clear hyp ; (* If non dependent, don't clear it! *) fail 1)) ;
        case hyp ; clear hyp
    | block ?T => fail 1 (* Do not put any part of the rhs in the hyps *)
    | forall x, _ => intro x || (let H := fresh x in rename x into H ; intro x) (* Try to keep original names *)
    | _ => intro
  end.

Ltac simplify_one_dep_elim :=
  match goal with
    | [ |- ?gl ] => simplify_one_dep_elim_term gl
  end.

(** Repeat until no progress is possible. By construction, it should leave the goal with
   no remaining equalities generated by the [generalize_eqs] tactic. *)

Ltac simplify_dep_elim := repeat simplify_one_dep_elim.

(** Do dependent elimination of the last hypothesis, but not simplifying yet
   (used internally). *)

Ltac destruct_last :=
  on_last_hyp ltac:(fun id => simpl in id ; generalize_eqs id ; destruct id).

Ltac introduce p := first [
  match p with _ => (* Already there, generalize dependent hyps *)
    generalize dependent p ; intros p
  end
  | intros until p | intros until 1 | intros ].

Ltac do_case p := introduce p ; (destruct p || elim_case p || (case p ; clear p)).
Ltac do_ind p := introduce p ; (induction p || elim_ind p).

(** The following tactics allow to do induction on an already instantiated inductive predicate
   by first generalizing it and adding the proper equalities to the context, in a maner similar to
   the BasicElim tactic of "Elimination with a motive" by Conor McBride. *)

(** The [do_depelim] higher-order tactic takes an elimination tactic as argument and an hypothesis 
   and starts a dependent elimination using this tactic. *)

Ltac is_introduced H :=
  match goal with
    | [ H' : _ |- _ ] => match H' with H => idtac end
  end.

Tactic Notation "intro_block" hyp(H) :=
  (is_introduced H ; block_goal ; revert_until H) ||
    (let H' := fresh H in intros until H' ; block_goal) || (intros ; block_goal).

Tactic Notation "intro_block_id" ident(H) :=
  (is_introduced H ; block_goal ; revert_until H) ||
    (let H' := fresh H in intros until H' ; block_goal) || (intros ; block_goal).

Ltac simpl_dep_elim := simplify_dep_elim ; simplify_IH_hyps ; unblock_all.

Ltac do_intros H :=
  (try intros until H) ; (intro_block_id H || intro_block H).

Ltac do_depelim_nosimpl tac H := do_intros H ; generalize_eqs H ; block_goal ; tac H ; unblock_goal.

Ltac do_depelim tac H := do_depelim_nosimpl tac H ; simpl_dep_elim.

Ltac do_depind tac H := 
  do_intros H ; generalize_eqs_vars H ; block_goal ; tac H ; 
  unblock_goal ; simplify_dep_elim ; simplify_IH_hyps ; unblock_all.

(** To dependent elimination on some hyp. *)

Ltac depelim id := do_depelim ltac:(fun hyp => do_case hyp) id.

(** Used internally. *)

Ltac depelim_nosimpl id := do_depelim_nosimpl ltac:(fun hyp => do_case hyp) id.

(** To dependent induction on some hyp. *)

Ltac depind id := do_depind ltac:(fun hyp => do_ind hyp) id.

(** A variant where generalized variables should be given by the user. *)

Ltac do_depelim' tac H :=
  (try intros until H) ; block_goal ; generalize_eqs H ; block_goal ; tac H ; unblock_goal ;
    simplify_dep_elim ; simplify_IH_hyps ; unblock_all.

(** Calls [destruct] on the generalized hypothesis, results should be similar to inversion.
   By default, we don't try to generalize the hyp by its variable indices.  *)

Tactic Notation "dependent" "destruction" ident(H) := 
  do_depelim' ltac:(fun hyp => do_case hyp) H.

Tactic Notation "dependent" "destruction" ident(H) "using" constr(c) := 
  do_depelim' ltac:(fun hyp => destruct hyp using c) H.

(** This tactic also generalizes the goal by the given variables before the elimination. *)

Tactic Notation "dependent" "destruction" ident(H) "generalizing" ne_hyp_list(l) := 
  do_depelim' ltac:(fun hyp => revert l ; do_case hyp) H.

Tactic Notation "dependent" "destruction" ident(H) "generalizing" ne_hyp_list(l) "using" constr(c) := 
  do_depelim' ltac:(fun hyp => revert l ; destruct hyp using c) H.

(** Then we have wrappers for usual calls to induction. One can customize the induction tactic by 
   writting another wrapper calling do_depelim. We suppose the hyp has to be generalized before
   calling [induction]. *)

Tactic Notation "dependent" "induction" ident(H) :=
  do_depind ltac:(fun hyp => do_ind hyp) H.

Tactic Notation "dependent" "induction" ident(H) "using" constr(c) :=
  do_depind ltac:(fun hyp => induction hyp using c) H.

(** This tactic also generalizes the goal by the given variables before the induction. *)

Tactic Notation "dependent" "induction" ident(H) "generalizing" ne_hyp_list(l) := 
  do_depelim' ltac:(fun hyp => generalize l ; clear l ; do_ind hyp) H.

Tactic Notation "dependent" "induction" ident(H) "generalizing" ne_hyp_list(l) "using" constr(c) := 
  do_depelim' ltac:(fun hyp => generalize l ; clear l ; induction hyp using c) H.
