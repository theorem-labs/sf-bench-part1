From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
From Stdlib Require Import Logic.ProofIrrelevance.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
#[local] Set Printing Coercions.

From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__aexp__iso Isomorphisms.nat__iso.
From IsomorphismChecker Require Export Isomorphisms.U_nat__add__iso Isomorphisms.U_nat__sub__iso Isomorphisms.U_nat__mul__iso.

Monomorphic Definition imported_Original_LF__DOT__Imp_LF_Imp_AExp_aevalR : imported_Original_LF__DOT__Imp_LF_Imp_AExp_aexp -> imported_nat -> SProp := Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aevalR.

(* Helper lemma for nat_to_imported and add *)
Lemma nat_to_imported_add : forall n1 n2 : nat,
  nat_to_imported (n1 + n2) = Imported.Nat_add (nat_to_imported n1) (nat_to_imported n2).
Proof.
  intros n1 n2.
  assert (Hrel1 : rel_iso nat_iso n1 (nat_to_imported n1)) by (constructor; apply IsomorphismDefinitions.eq_refl).
  assert (Hrel2 : rel_iso nat_iso n2 (nat_to_imported n2)) by (constructor; apply IsomorphismDefinitions.eq_refl).
  pose proof (@Nat_add_iso n1 (nat_to_imported n1) Hrel1 n2 (nat_to_imported n2) Hrel2) as H.
  destruct H as [Heq]. apply eq_of_seq in Heq. exact Heq.
Qed.

Lemma nat_to_imported_sub : forall n1 n2 : nat,
  nat_to_imported (n1 - n2) = Imported.Nat_sub (nat_to_imported n1) (nat_to_imported n2).
Proof.
  intros n1 n2.
  assert (Hrel1 : rel_iso nat_iso n1 (nat_to_imported n1)) by (constructor; apply IsomorphismDefinitions.eq_refl).
  assert (Hrel2 : rel_iso nat_iso n2 (nat_to_imported n2)) by (constructor; apply IsomorphismDefinitions.eq_refl).
  pose proof (@Nat_sub_iso n1 (nat_to_imported n1) Hrel1 n2 (nat_to_imported n2) Hrel2) as H.
  destruct H as [Heq]. apply eq_of_seq in Heq. exact Heq.
Qed.

Lemma nat_to_imported_mul : forall n1 n2 : nat,
  nat_to_imported (n1 * n2) = Imported.Nat_mul (nat_to_imported n1) (nat_to_imported n2).
Proof.
  intros n1 n2.
  assert (Hrel1 : rel_iso nat_iso n1 (nat_to_imported n1)) by (constructor; apply IsomorphismDefinitions.eq_refl).
  assert (Hrel2 : rel_iso nat_iso n2 (nat_to_imported n2)) by (constructor; apply IsomorphismDefinitions.eq_refl).
  pose proof (@Nat_mul_iso n1 (nat_to_imported n1) Hrel1 n2 (nat_to_imported n2) Hrel2) as H.
  destruct H as [Heq]. apply eq_of_seq in Heq. exact Heq.
Qed.

(* Helper: Prop to SProp direction *)
Lemma aevalR_Prop_to_SProp : forall (x1 : Original.LF_DOT_Imp.LF.Imp.AExp.aexp) (x3 : nat),
  Original.LF_DOT_Imp.LF.Imp.AExp.aevalR x1 x3 ->
  Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aevalR (aexp_to_imported x1) (nat_to_imported x3).
Proof.
  intros x1 x3 H.
  induction H.
  - apply Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aevalR_E_ANum.
  - simpl aexp_to_imported. rewrite nat_to_imported_add.
    apply Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aevalR_E_APlus; assumption.
  - simpl aexp_to_imported. rewrite nat_to_imported_sub.
    apply Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aevalR_E_AMinus; assumption.
  - simpl aexp_to_imported. rewrite nat_to_imported_mul.
    apply Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aevalR_E_AMult; assumption.
Qed.

(* Helper lemmas for imported_to_nat compatibility *)
Lemma imported_to_nat_add_compat : forall n1 n2,
  imported_to_nat (Imported.Nat_add n1 n2) = imported_to_nat n1 + imported_to_nat n2.
Proof.
  intros n1 n2.
  pose proof (nat_iso.(from_to) (imported_to_nat n1 + imported_to_nat n2)) as Hft.
  apply eq_of_seq in Hft.
  pose proof (nat_iso.(to_from) n1) as Htf1.
  pose proof (nat_iso.(to_from) n2) as Htf2.
  apply eq_of_seq in Htf1. apply eq_of_seq in Htf2.
  assert (Hrel1 : rel_iso nat_iso (imported_to_nat n1) n1).
  { constructor. apply seq_of_eq. exact Htf1. }
  assert (Hrel2 : rel_iso nat_iso (imported_to_nat n2) n2).
  { constructor. apply seq_of_eq. exact Htf2. }
  pose proof (@Nat_add_iso (imported_to_nat n1) n1 Hrel1 (imported_to_nat n2) n2 Hrel2) as H.
  destruct H as [Heq].
  apply eq_of_seq in Heq.
  (* Heq : nat_to_imported (imported_to_nat n1 + imported_to_nat n2) = imported_Nat_add n1 n2 *)
  (* imported_Nat_add = Imported.Nat_add, so we need to unfold *)
  unfold imported_Nat_add in Heq.
  rewrite <- Heq. exact Hft.
Qed.

Lemma imported_to_nat_sub_compat : forall n1 n2,
  imported_to_nat (Imported.Nat_sub n1 n2) = imported_to_nat n1 - imported_to_nat n2.
Proof.
  intros n1 n2.
  pose proof (nat_iso.(from_to) (imported_to_nat n1 - imported_to_nat n2)) as Hft.
  apply eq_of_seq in Hft.
  pose proof (nat_iso.(to_from) n1) as Htf1.
  pose proof (nat_iso.(to_from) n2) as Htf2.
  apply eq_of_seq in Htf1. apply eq_of_seq in Htf2.
  assert (Hrel1 : rel_iso nat_iso (imported_to_nat n1) n1).
  { constructor. apply seq_of_eq. exact Htf1. }
  assert (Hrel2 : rel_iso nat_iso (imported_to_nat n2) n2).
  { constructor. apply seq_of_eq. exact Htf2. }
  pose proof (@Nat_sub_iso (imported_to_nat n1) n1 Hrel1 (imported_to_nat n2) n2 Hrel2) as H.
  destruct H as [Heq].
  apply eq_of_seq in Heq.
  unfold imported_Nat_sub in Heq.
  rewrite <- Heq. exact Hft.
Qed.

Lemma imported_to_nat_mul_compat : forall n1 n2,
  imported_to_nat (Imported.Nat_mul n1 n2) = imported_to_nat n1 * imported_to_nat n2.
Proof.
  intros n1 n2.
  pose proof (nat_iso.(from_to) (imported_to_nat n1 * imported_to_nat n2)) as Hft.
  apply eq_of_seq in Hft.
  pose proof (nat_iso.(to_from) n1) as Htf1.
  pose proof (nat_iso.(to_from) n2) as Htf2.
  apply eq_of_seq in Htf1. apply eq_of_seq in Htf2.
  assert (Hrel1 : rel_iso nat_iso (imported_to_nat n1) n1).
  { constructor. apply seq_of_eq. exact Htf1. }
  assert (Hrel2 : rel_iso nat_iso (imported_to_nat n2) n2).
  { constructor. apply seq_of_eq. exact Htf2. }
  pose proof (@Nat_mul_iso (imported_to_nat n1) n1 Hrel1 (imported_to_nat n2) n2 Hrel2) as H.
  destruct H as [Heq].
  apply eq_of_seq in Heq.
  unfold imported_Nat_mul in Heq.
  rewrite <- Heq. exact Hft.
Qed.

(* Helper: SProp to Prop direction *)
Lemma aevalR_SProp_to_Prop : forall (x2 : imported_Original_LF__DOT__Imp_LF_Imp_AExp_aexp) (x4 : imported_nat),
  imported_Original_LF__DOT__Imp_LF_Imp_AExp_aevalR x2 x4 ->
  SInhabited (Original.LF_DOT_Imp.LF.Imp.AExp.aevalR (imported_to_aexp x2) (imported_to_nat x4)).
Proof.
  intros x2 x4 H.
  induction H using Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aevalR_sind.
  - apply sinhabits. simpl. apply Original.LF_DOT_Imp.LF.Imp.AExp.E_ANum.
  - destruct IHOriginal_LF__DOT__Imp_LF_Imp_AExp_aevalR1 as [H1'].
    destruct IHOriginal_LF__DOT__Imp_LF_Imp_AExp_aevalR2 as [H2'].
    apply sinhabits. simpl.
    replace (imported_to_nat (Imported.Nat_add n1 n2)) with (imported_to_nat n1 + imported_to_nat n2)
      by (symmetry; apply imported_to_nat_add_compat).
    apply Original.LF_DOT_Imp.LF.Imp.AExp.E_APlus; assumption.
  - destruct IHOriginal_LF__DOT__Imp_LF_Imp_AExp_aevalR1 as [H1'].
    destruct IHOriginal_LF__DOT__Imp_LF_Imp_AExp_aevalR2 as [H2'].
    apply sinhabits. simpl.
    replace (imported_to_nat (Imported.Nat_sub n1 n2)) with (imported_to_nat n1 - imported_to_nat n2)
      by (symmetry; apply imported_to_nat_sub_compat).
    apply Original.LF_DOT_Imp.LF.Imp.AExp.E_AMinus; assumption.
  - destruct IHOriginal_LF__DOT__Imp_LF_Imp_AExp_aevalR1 as [H1'].
    destruct IHOriginal_LF__DOT__Imp_LF_Imp_AExp_aevalR2 as [H2'].
    apply sinhabits. simpl.
    replace (imported_to_nat (Imported.Nat_mul n1 n2)) with (imported_to_nat n1 * imported_to_nat n2)
      by (symmetry; apply imported_to_nat_mul_compat).
    apply Original.LF_DOT_Imp.LF.Imp.AExp.E_AMult; assumption.
Qed.

Lemma aevalR_to : forall x1 x2,
  aexp_to_imported x1 = x2 ->
  forall x3 x4,
  nat_to_imported x3 = x4 ->
  Original.LF_DOT_Imp.LF.Imp.AExp.aevalR x1 x3 ->
  imported_Original_LF__DOT__Imp_LF_Imp_AExp_aevalR x2 x4.
Proof.
  intros x1 x2 Heq1 x3 x4 Heq2 HP.
  subst x2 x4.
  apply aevalR_Prop_to_SProp. exact HP.
Qed.

Lemma imported_to_aexp_to (x : Original.LF_DOT_Imp.LF.Imp.AExp.aexp) :
  imported_to_aexp (aexp_to_imported x) = x.
Proof.
  pose proof (Original_LF__DOT__Imp_LF_Imp_AExp_aexp_iso.(from_to) x) as H.
  apply eq_of_seq in H. exact H.
Qed.

Lemma imported_to_nat_to (x : nat) : imported_to_nat (nat_to_imported x) = x.
Proof.
  pose proof (nat_iso.(from_to) x) as H.
  apply eq_of_seq in H. exact H.
Qed.

Lemma aevalR_from : forall x1 x2,
  aexp_to_imported x1 = x2 ->
  forall x3 x4,
  nat_to_imported x3 = x4 ->
  imported_Original_LF__DOT__Imp_LF_Imp_AExp_aevalR x2 x4 ->
  Original.LF_DOT_Imp.LF.Imp.AExp.aevalR x1 x3.
Proof.
  intros x1 x2 Heq1 x3 x4 Heq2 HS.
  apply sinhabitant.
  subst x2 x4.
  assert (Hinhab : SInhabited (Original.LF_DOT_Imp.LF.Imp.AExp.aevalR (imported_to_aexp (aexp_to_imported x1)) (imported_to_nat (nat_to_imported x3)))).
  { exact (@aevalR_SProp_to_Prop (aexp_to_imported x1) (nat_to_imported x3) HS). }
  (* We need to convert this to SInhabited (aevalR x1 x3) *)
  rewrite imported_to_aexp_to, imported_to_nat_to in Hinhab.
  exact Hinhab.
Qed.

Monomorphic Instance Original_LF__DOT__Imp_LF_Imp_AExp_aevalR_iso : forall (x1 : Original.LF_DOT_Imp.LF.Imp.AExp.aexp) (x2 : imported_Original_LF__DOT__Imp_LF_Imp_AExp_aexp),
  rel_iso Original_LF__DOT__Imp_LF_Imp_AExp_aexp_iso x1 x2 ->
  forall (x3 : nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> Iso (Original.LF_DOT_Imp.LF.Imp.AExp.aevalR x1 x3) (imported_Original_LF__DOT__Imp_LF_Imp_AExp_aevalR x2 x4).
Proof.
  intros x1 x2 Hr1 x3 x4 Hr2.
  destruct Hr1 as [Heq1]. destruct Hr2 as [Heq2].
  apply eq_of_seq in Heq1. apply eq_of_seq in Heq2.
  subst x2 x4.
  unshelve econstructor.
  - exact (@aevalR_Prop_to_SProp x1 x3).
  - exact (@aevalR_from x1 (aexp_to_imported x1) Logic.eq_refl x3 (nat_to_imported x3) Logic.eq_refl).
  - intro s. apply IsomorphismDefinitions.eq_refl.
  - intro p. apply seq_of_peq_t. apply proof_irrelevance.
Defined.
Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.AExp.aevalR := {}.
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aevalR := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.AExp.aevalR Original_LF__DOT__Imp_LF_Imp_AExp_aevalR_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.AExp.aevalR Imported.Original_LF__DOT__Imp_LF_Imp_AExp_aevalR Original_LF__DOT__Imp_LF_Imp_AExp_aevalR_iso := {}.
