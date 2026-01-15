From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Monomorphic Definition imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2 : imported_nat -> imported_nat -> SProp := Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2.

(* Helper: nat_iso is injective *)
Lemma nat_iso_inj : forall n m, nat_iso n = nat_iso m -> n = m.
Proof.
  induction n; destruct m; simpl; intros H.
  - reflexivity.
  - discriminate.
  - discriminate.
  - f_equal. apply IHn. injection H. auto.
Qed.

(* Forward direction - simplified version *)
Lemma le2_fwd' : forall (n m : nat),
  Original.LF_DOT_IndPrinciples.LF.IndPrinciples.le2 n m -> 
  imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2 (nat_iso n) (nat_iso m).
Proof.
  intros n m Hle.
  induction Hle.
  - apply Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2_le2_n.
  - change (nat_iso (S m)) with (Imported.nat_S (nat_iso m)).
    apply Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2_le2_S.
    exact IHHle.
Qed.

Lemma le2_fwd (x1 : nat) (x2 : imported_nat) (h1 : rel_iso nat_iso x1 x2)
              (x3 : nat) (x4 : imported_nat) (h3 : rel_iso nat_iso x3 x4) :
  Original.LF_DOT_IndPrinciples.LF.IndPrinciples.le2 x1 x3 -> 
  imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2 x2 x4.
Proof.
  destruct h1 as [h1], h3 as [h3].
  rewrite <- (eq_of_seq h1), <- (eq_of_seq h3).
  apply le2_fwd'.
Qed.
Arguments le2_fwd : clear implicits.

(* Backward direction - need SInhabited trick for SProp -> Prop *)
(* Helper for inverse: imported_nat -> nat *)
Fixpoint imported_nat_to_nat (x : imported_nat) : nat :=
  match x with
  | Imported.nat_O => O
  | Imported.nat_S n => S (imported_nat_to_nat n)
  end.

Lemma nat_iso_inv : forall n, imported_nat_to_nat (nat_iso n) = n.
Proof. induction n; simpl; [reflexivity | f_equal; assumption]. Qed.

Lemma nat_iso_inv' : forall x, nat_iso (imported_nat_to_nat x) = x.
Proof. induction x; simpl; [reflexivity | f_equal; assumption]. Qed.

(* Generalize: work on imported_nat *)
Lemma le2_bwd_sinhabited_aux : forall (x y : imported_nat),
  imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2 x y -> 
  SInhabited (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.le2 (imported_nat_to_nat x) (imported_nat_to_nat y)).
Proof.
  intros x y Hle.
  induction Hle.
  - apply sinhabits.
    apply Original.LF_DOT_IndPrinciples.LF.IndPrinciples.le2_n.
  - destruct IHHle as [IH].
    apply sinhabits.
    simpl.
    apply Original.LF_DOT_IndPrinciples.LF.IndPrinciples.le2_S.
    exact IH.
Qed.

Lemma le2_bwd' : forall (n m : nat),
  imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2 (nat_iso n) (nat_iso m) -> 
  Original.LF_DOT_IndPrinciples.LF.IndPrinciples.le2 n m.
Proof.
  intros n m H.
  apply sinhabitant.
  assert (SInhabited (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.le2 (imported_nat_to_nat (nat_iso n)) (imported_nat_to_nat (nat_iso m)))) as Haux.
  { apply le2_bwd_sinhabited_aux. exact H. }
  rewrite !nat_iso_inv in Haux.
  exact Haux.
Qed.

Lemma le2_bwd (x1 : nat) (x2 : imported_nat) (h1 : rel_iso nat_iso x1 x2)
              (x3 : nat) (x4 : imported_nat) (h3 : rel_iso nat_iso x3 x4) :
  imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2 x2 x4 -> 
  Original.LF_DOT_IndPrinciples.LF.IndPrinciples.le2 x1 x3.
Proof.
  destruct h1 as [h1], h3 as [h3].
  intro Hle.
  (* h1 : eq (nat_iso x1) x2 means nat_iso x1 = x2 *)
  (* We want to replace x2 with nat_iso x1 in Hle, so use <- *)
  rewrite <- (eq_of_seq h1), <- (eq_of_seq h3) in Hle.
  apply le2_bwd'. exact Hle.
Qed.
Arguments le2_bwd : clear implicits.

(* Helper for proof irrelevance in SProp *)
Lemma from_to_helper : forall (x1 : nat) (x2 : imported_nat) (h1 : rel_iso nat_iso x1 x2)
        (x3 : nat) (x4 : imported_nat) (h3 : rel_iso nat_iso x3 x4)
        (x : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.le2 x1 x3),
  IsomorphismDefinitions.eq (le2_bwd x1 x2 h1 x3 x4 h3 (le2_fwd x1 x2 h1 x3 x4 h3 x)) x.
Proof.
  intros.
  apply seq_of_eq.
  apply ProofIrrelevance.proof_irrelevance.
Defined.

Monomorphic Instance Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 ->
  forall (x3 : nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> Iso (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.le2 x1 x3) (imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2 x2 x4).
Proof.
  intros x1 x2 h1 x3 x4 h3.
  apply Build_Iso with (to := le2_fwd x1 x2 h1 x3 x4 h3) (from := le2_bwd x1 x2 h1 x3 x4 h3).
  - (* to_from: SProp values are proof irrelevant *)
    intro x. apply IsomorphismDefinitions.eq_refl.
  - (* from_to: Prop, use proof irrelevance *)
    intro x.
    apply from_to_helper.
Defined.

Instance: KnownConstant Original.LF_DOT_IndPrinciples.LF.IndPrinciples.le2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndPrinciples.LF.IndPrinciples.le2 Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndPrinciples.LF.IndPrinciples.le2 Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2 Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2_iso := {}.
