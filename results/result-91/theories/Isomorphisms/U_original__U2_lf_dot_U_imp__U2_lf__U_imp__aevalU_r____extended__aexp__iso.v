From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
From IsomorphismChecker Require Export Isomorphisms.nat__iso.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp : Type := Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp.

(* Convert from original aexp to imported aexp *)
Fixpoint aexp_to_imported (a : Original.LF_DOT_Imp.LF.Imp.aevalR_extended.aexp) : Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp :=
  match a with
  | Original.LF_DOT_Imp.LF.Imp.aevalR_extended.AAny => 
      Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_AAny
  | Original.LF_DOT_Imp.LF.Imp.aevalR_extended.ANum n => 
      Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_ANum (nat_to_imported n)
  | Original.LF_DOT_Imp.LF.Imp.aevalR_extended.APlus a1 a2 => 
      Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_APlus (aexp_to_imported a1) (aexp_to_imported a2)
  | Original.LF_DOT_Imp.LF.Imp.aevalR_extended.AMinus a1 a2 => 
      Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_AMinus (aexp_to_imported a1) (aexp_to_imported a2)
  | Original.LF_DOT_Imp.LF.Imp.aevalR_extended.AMult a1 a2 => 
      Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_AMult (aexp_to_imported a1) (aexp_to_imported a2)
  end.

(* Convert from imported aexp to original aexp *)
Fixpoint imported_to_aexp (a : Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp) : Original.LF_DOT_Imp.LF.Imp.aevalR_extended.aexp :=
  match a with
  | Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_AAny => 
      Original.LF_DOT_Imp.LF.Imp.aevalR_extended.AAny
  | Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_ANum n => 
      Original.LF_DOT_Imp.LF.Imp.aevalR_extended.ANum (imported_to_nat n)
  | Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_APlus a1 a2 => 
      Original.LF_DOT_Imp.LF.Imp.aevalR_extended.APlus (imported_to_aexp a1) (imported_to_aexp a2)
  | Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_AMinus a1 a2 => 
      Original.LF_DOT_Imp.LF.Imp.aevalR_extended.AMinus (imported_to_aexp a1) (imported_to_aexp a2)
  | Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_AMult a1 a2 => 
      Original.LF_DOT_Imp.LF.Imp.aevalR_extended.AMult (imported_to_aexp a1) (imported_to_aexp a2)
  end.

(* Congruence lemmas for IsomorphismDefinitions.eq *)
Lemma ANum_cong : forall x y : Imported.nat,
  IsomorphismDefinitions.eq x y ->
  IsomorphismDefinitions.eq 
    (Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_ANum x)
    (Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_ANum y).
Proof. intros x y H. destruct H. apply IsomorphismDefinitions.eq_refl. Qed.

Lemma ANum_cong_orig : forall x y : Datatypes.nat,
  IsomorphismDefinitions.eq x y ->
  IsomorphismDefinitions.eq 
    (Original.LF_DOT_Imp.LF.Imp.aevalR_extended.ANum x)
    (Original.LF_DOT_Imp.LF.Imp.aevalR_extended.ANum y).
Proof. intros x y H. destruct H. apply IsomorphismDefinitions.eq_refl. Qed.

Lemma APlus_cong : forall x1 y1 x2 y2 : Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp,
  IsomorphismDefinitions.eq x1 y1 -> IsomorphismDefinitions.eq x2 y2 ->
  IsomorphismDefinitions.eq 
    (Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_APlus x1 x2)
    (Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_APlus y1 y2).
Proof. intros. destruct H. destruct H0. apply IsomorphismDefinitions.eq_refl. Qed.

Lemma APlus_cong_orig : forall x1 y1 x2 y2 : Original.LF_DOT_Imp.LF.Imp.aevalR_extended.aexp,
  IsomorphismDefinitions.eq x1 y1 -> IsomorphismDefinitions.eq x2 y2 ->
  IsomorphismDefinitions.eq 
    (Original.LF_DOT_Imp.LF.Imp.aevalR_extended.APlus x1 x2)
    (Original.LF_DOT_Imp.LF.Imp.aevalR_extended.APlus y1 y2).
Proof. intros. destruct H. destruct H0. apply IsomorphismDefinitions.eq_refl. Qed.

Lemma AMinus_cong : forall x1 y1 x2 y2 : Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp,
  IsomorphismDefinitions.eq x1 y1 -> IsomorphismDefinitions.eq x2 y2 ->
  IsomorphismDefinitions.eq 
    (Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_AMinus x1 x2)
    (Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_AMinus y1 y2).
Proof. intros. destruct H. destruct H0. apply IsomorphismDefinitions.eq_refl. Qed.

Lemma AMinus_cong_orig : forall x1 y1 x2 y2 : Original.LF_DOT_Imp.LF.Imp.aevalR_extended.aexp,
  IsomorphismDefinitions.eq x1 y1 -> IsomorphismDefinitions.eq x2 y2 ->
  IsomorphismDefinitions.eq 
    (Original.LF_DOT_Imp.LF.Imp.aevalR_extended.AMinus x1 x2)
    (Original.LF_DOT_Imp.LF.Imp.aevalR_extended.AMinus y1 y2).
Proof. intros. destruct H. destruct H0. apply IsomorphismDefinitions.eq_refl. Qed.

Lemma AMult_cong : forall x1 y1 x2 y2 : Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp,
  IsomorphismDefinitions.eq x1 y1 -> IsomorphismDefinitions.eq x2 y2 ->
  IsomorphismDefinitions.eq 
    (Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_AMult x1 x2)
    (Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_AMult y1 y2).
Proof. intros. destruct H. destruct H0. apply IsomorphismDefinitions.eq_refl. Qed.

Lemma AMult_cong_orig : forall x1 y1 x2 y2 : Original.LF_DOT_Imp.LF.Imp.aevalR_extended.aexp,
  IsomorphismDefinitions.eq x1 y1 -> IsomorphismDefinitions.eq x2 y2 ->
  IsomorphismDefinitions.eq 
    (Original.LF_DOT_Imp.LF.Imp.aevalR_extended.AMult x1 x2)
    (Original.LF_DOT_Imp.LF.Imp.aevalR_extended.AMult y1 y2).
Proof. intros. destruct H. destruct H0. apply IsomorphismDefinitions.eq_refl. Qed.

Lemma aexp_to_from : forall x : Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp,
  IsomorphismDefinitions.eq (aexp_to_imported (imported_to_aexp x)) x.
Proof.
  intro x. induction x.
  - simpl. apply IsomorphismDefinitions.eq_refl.
  - simpl. apply ANum_cong. apply nat_to_from.
  - simpl. apply APlus_cong; assumption.
  - simpl. apply AMinus_cong; assumption.
  - simpl. apply AMult_cong; assumption.
Qed.

Lemma aexp_from_to : forall x : Original.LF_DOT_Imp.LF.Imp.aevalR_extended.aexp,
  IsomorphismDefinitions.eq (imported_to_aexp (aexp_to_imported x)) x.
Proof.
  intro x. induction x.
  - simpl. apply IsomorphismDefinitions.eq_refl.
  - simpl. apply ANum_cong_orig. apply nat_from_to.
  - simpl. apply APlus_cong_orig; assumption.
  - simpl. apply AMinus_cong_orig; assumption.
  - simpl. apply AMult_cong_orig; assumption.
Qed.

Instance Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_iso : Iso Original.LF_DOT_Imp.LF.Imp.aevalR_extended.aexp imported_Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp :=
  @Build_Iso _ _ aexp_to_imported imported_to_aexp aexp_to_from aexp_from_to.

Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.aevalR_extended.aexp := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.aevalR_extended.aexp Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.aevalR_extended.aexp Imported.Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_iso := {}.