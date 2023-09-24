Require Import List PeanoNat Compare_dec EqNat Decidable ListDec.
Require Fin.
Set Implicit Arguments.

(** General definitions *)

Definition Injective {A B} (f : A->B) :=
 forall x y, f x = f y -> x = y.

Definition Surjective {A B} (f : A->B) :=
 forall y, exists x, f x = y.

Definition Bijective {A B} (f : A->B) :=
 exists g:B->A, (forall x, g (f x) = x) /\ (forall y, f (g y) = y).

Definition Full {A:Type} (l:list A) := forall a:A, In a l.
Definition Finite (A:Type) := exists (l:list A), Full l.

Definition Listing {A:Type} (l:list A) := NoDup l /\ Full l.
Definition Finite' (A:Type) := exists (l:list A), Listing l.

Lemma Listing_decidable_eq {A:Type} (l:list A): Listing l -> decidable_eq A.
Proof.
  intro hl.
  red in hl.
  destruct hl as [ Hnodup Hfull ].
  intros x y.
  assert (lem1:=NoDup_list_decidable).
  specialize (lem1 A l).
  specialize (lem1 Hnodup).
  apply lem1.
  all:red in Hfull.
  all:apply Hfull.
Qed.

Lemma Finite_dec {A:Type}: Finite A /\ decidable_eq A <-> Finite' A.
Proof.
  split.
  {
    intros [ hfin hdec ].
    red.
    red in hfin.
    assert (lem1:=uniquify).
    specialize (lem1 A).
    specialize (lem1 hdec).
    destruct hfin as [ l hfull ].
    specialize (lem1 l).
    destruct lem1 as [ l' hl' ].
    exists l'.
    red.
    destruct hl' as [ hnodup hincl ].
    split.
    { exact hnodup. }
    {
      red in hincl.
      red.
      red in hfull.
      intro x.
      apply hincl.
      apply hfull.
    }
  }
  {
    intro hfin.
    red in hfin.
    destruct hfin as [ l hl ].
    split.
    {
      red in hl.
      destruct hl as [ hnodup hfull ].
      red.
      exists l.
      exact hfull.
    }
    {
      eapply Listing_decidable_eq.
      exact hl.
    }
  }
Qed.

(** Injections characterized in term of lists *)

Lemma Injective_map_NoDup A B (f:A->B) (l:list A) :
 Injective f -> NoDup l -> NoDup (map f l).
Proof.
  intros Ij.
  red in Ij.
  induction 1 as [|x l X N IH].
  all:simpl.
  { constructor. }
  {
    constructor.
    2:assumption.
    assert (lem1:=in_map_iff).
    red.
    intro hin.
    apply lem1 in hin.
    clear lem1.
    destruct hin as [y [ E Y ] ].
    apply Ij in E.
    clear Ij.
    subst y.
    red in X.
    apply X.
    exact Y.
  }
Qed.

Lemma Injective_list_carac A B (d:decidable_eq A)(f:A->B) :
  Injective f <-> (forall l, NoDup l -> NoDup (map f l)).
Proof.
  split.
  {
    intro hinj.
    intro l.
    apply Injective_map_NoDup.
    exact hinj.
  }
  {
   intros H x y E.
   red in d.
   specialize (d x y).
   red in d.
    destruct d as [ heq | hneq ].
    { subst y. reflexivity. }
    {
      assert (N : NoDup (x::y::nil)).
      {
        constructor.
        {
          simpl.
          red.
          intro h.
          destruct h as [ hl | hr ].
          { subst y. apply hneq. reflexivity. }
          { destruct hr. }
        }
        {
          constructor.
          { simpl. red.  destruct 1. }
          { constructor. }
        }
      }
      specialize (H _ N).
      simpl in H.
      rewrite E in H.
      inversion_clear H.
      simpl in *.
      red in H0.
      exfalso. apply H0. left. reflexivity.
    }
  }
Qed.

Lemma Injective_carac A B (l:list A) : Listing l ->
   forall (f:A->B), Injective f <-> NoDup (map f l).
Proof.
 intros L f. split.
 - intros Ij. apply Injective_map_NoDup. assumption. destruct L. assumption.
 - intros N x y E.
   assert (X : In x l). red in L. destruct L. red in H0. apply H0.
   assert (Y : In y l). red in L. destruct L. red in H0. apply H0.
   apply In_nth_error in X. destruct X as (i,X).
   apply In_nth_error in Y. destruct Y as (j,Y).
   assert (X' := map_nth_error f _ _ X).
   assert (Y' := map_nth_error f _ _ Y).
   assert (i = j).
   { rewrite NoDup_nth_error in N. apply N.
     - rewrite <- nth_error_Some. now rewrite X'.
     - rewrite X', Y'. now f_equal. }
   subst j. rewrite Y in X. now injection X.
Qed.

(** Surjection characterized in term of lists *)

Lemma Surjective_list_carac A B (f:A->B):
  Surjective f <-> (forall lB, exists lA, incl lB (map f lA)).
Proof.
 split.
 - intros Su lB.
   induction lB as [|b lB IH].
   + now exists nil.
   + destruct (Su b) as (a,E).
     destruct IH as (lA,IC).
     exists (a::lA). simpl. rewrite E.
     intros x [X|X]; simpl; intuition.
 - intros H y.
   destruct (H (y::nil)) as (lA,IC).
   assert (IN : In y (map f lA)) by (apply (IC y); now left).
   rewrite in_map_iff in IN. destruct IN as (x & E & _).
   now exists x.
Qed.

Lemma Surjective_carac A B : Finite B -> decidable_eq B ->
  forall f:A->B, Surjective f <-> (exists lA, Listing (map f lA)).
Proof.
 intros (lB,FB) d f. split.
 - rewrite Surjective_list_carac.
   intros Su. destruct (Su lB) as (lA,IC).
   destruct (uniquify_map d f lA) as (lA' & N & IC').
   exists lA'. split; trivial.
   intro x. apply IC', IC, FB.
 - intros (lA & N & FA) y.
   generalize (FA y). rewrite in_map_iff. intros (x & E & _).
   now exists x.
Qed.

(** Main result : *)

Lemma Endo_Injective_Surjective :
 forall A, Finite A -> decidable_eq A ->
  forall f:A->A, Injective f <-> Surjective f.
Proof.
 intros A F d f. rewrite (Surjective_carac F d). split.
 - assert (Finite' A) as (l, L) by (now apply Finite_dec); clear F.
   rewrite (Injective_carac L); intros.
   exists l; split; trivial.
   destruct L as (N,F).
   assert (I : incl l (map f l)).
   { apply NoDup_length_incl; trivial.
     - now rewrite map_length.
     - intros x _. apply F. }
   intros x. apply I, F.
 - clear F d. intros (l,L).
   assert (N : NoDup l). { apply (NoDup_map_inv f), L. }
   assert (I : incl (map f l) l).
   { apply NoDup_length_incl; trivial.
     - now rewrite map_length.
     - intros x _. apply L. }
   assert (L' : Listing l).
   { split; trivial.
     intro x. apply I, L. }
   apply (Injective_carac L'), L.
Qed.


Lemma Fin_Finite n : Finite (Fin.t n).
Proof.
 induction n as [|n IHn].
 - exists nil.
   red;inversion 1.
 - destruct IHn as (l,Hl).
   exists (Fin.F1 :: map Fin.FS l).
   intros a. revert n a l Hl.
   refine (@Fin.caseS _ _ _); intros.
   + now left.
   + right. now apply in_map.
Qed.

Definition bFun n (f:nat->nat) := forall x, x < n -> f x < n.

Definition bInjective n (f:nat->nat) :=
 forall x y, x < n -> y < n -> f x = f y -> x = y.

Definition bSurjective n (f:nat->nat) :=
 forall y, y < n -> exists x, x < n /\ f x = y.

(** We show that this is equivalent to the use of [Fin.t n]. *)

Module Fin2Restrict.

Notation n2f := Fin.of_nat_lt.
Definition f2n {n} (x:Fin.t n) := proj1_sig (Fin.to_nat x).
Definition f2n_ok n (x:Fin.t n) : f2n x < n := proj2_sig (Fin.to_nat x).
Definition f2n_n2f x n h : f2n (n2f h) = x := f_equal (@proj1_sig _ _) (@Fin.to_nat_of_nat x n h).
Definition n2f_ext : forall x n h h', n2f h = n2f h' := @Fin.of_nat_ext.
Definition f2n_inj : forall n x y, f2n x = f2n y -> x = y := @Fin.to_nat_inj.

Definition restrict n (f:nat->nat)(hf : bFun n f) : (Fin.t n -> Fin.t n) :=
 fun x => let (x',h) := Fin.to_nat x in n2f (hf _ h).

Lemma restrict_f2n n f hf (x:Fin.t n) :
 f2n (@restrict n f hf x) = f (f2n x).
Proof.
 unfold restrict, f2n. destruct (Fin.to_nat x) as (x',h); simpl.
 apply f2n_n2f.
Qed.

Lemma restrict_n2f n f hf x (h:x<n) :
 @restrict n f hf (n2f h) = n2f (hf _ h).
Proof.
 unfold restrict. generalize (f2n_n2f h). unfold f2n.
 destruct (Fin.to_nat (n2f h)) as (x',h'); simpl. intros ->.
 now apply n2f_ext.
Qed.

Lemma restrict_surjective n f h :
  Surjective (@restrict n f h) <-> bSurjective n f.
Proof.
 split.
 - intros hf y hy.
   destruct (hf (n2f hy)) as (x,Eq).
   exists (f2n x).
   split.
   + apply f2n_ok.
   + rewrite <- (restrict_f2n h), Eq. apply f2n_n2f.
 - intros hf y.
   destruct (hf _ (f2n_ok y)) as (x & hx & Eq).
   exists (n2f hx).
   apply f2n_inj. now rewrite restrict_f2n, f2n_n2f.
Qed.

Lemma restrict_injective n f h :
  Injective (@restrict n f h) <-> bInjective n f.
Proof.
 split.
 - intros hf x y hx hy Eq.
   rewrite <- (f2n_n2f hx), <- (f2n_n2f hy). f_equal.
   apply hf.
   rewrite 2 restrict_n2f.
   generalize (h x hx) (h y hy).
   rewrite Eq. apply n2f_ext.
 - intros hf x y Eq.
   apply f2n_inj. apply hf; try apply f2n_ok.
   now rewrite <- 2 (restrict_f2n h), Eq.
Qed.

End Fin2Restrict.
Import Fin2Restrict.

Lemma bInjective_bSurjective n (f:nat->nat) :
 bFun n f -> (bInjective n f <-> bSurjective n f).
Proof.
 intros h.
 rewrite <- (restrict_injective h), <- (restrict_surjective h).
 apply Endo_Injective_Surjective.
 - apply Fin_Finite.
 - intros x y. destruct (Fin.eq_dec x y); [left|right]; trivial.
Qed.
