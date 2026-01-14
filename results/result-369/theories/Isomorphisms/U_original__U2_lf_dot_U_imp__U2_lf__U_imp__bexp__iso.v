From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
From Stdlib Require Import String Ascii.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso. (* for speed *)

(* Import the aexp isomorphism *)
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso.

(* Helper to convert standard equality to SProp equality *)
Lemma prop_to_sprop_eq_bexp : forall {A : Type} (a b : A), a = b -> IsomorphismDefinitions.eq a b.
Proof. intros A a b H. subst b. exact IsomorphismDefinitions.eq_refl. Qed.

(* Now we can define the bexp isomorphism *)

Fixpoint bexp_to_imported (b : Original.LF_DOT_Imp.LF.Imp.bexp) : Imported.Original_LF__DOT__Imp_LF_Imp_bexp :=
  match b with
  | Original.LF_DOT_Imp.LF.Imp.BTrue => Imported.Original_LF__DOT__Imp_LF_Imp_bexp_BTrue
  | Original.LF_DOT_Imp.LF.Imp.BFalse => Imported.Original_LF__DOT__Imp_LF_Imp_bexp_BFalse
  | Original.LF_DOT_Imp.LF.Imp.BEq a1 a2 => Imported.Original_LF__DOT__Imp_LF_Imp_bexp_BEq (aexp_to_imported a1) (aexp_to_imported a2)
  | Original.LF_DOT_Imp.LF.Imp.BNeq a1 a2 => Imported.Original_LF__DOT__Imp_LF_Imp_bexp_BNeq (aexp_to_imported a1) (aexp_to_imported a2)
  | Original.LF_DOT_Imp.LF.Imp.BLe a1 a2 => Imported.Original_LF__DOT__Imp_LF_Imp_bexp_BLe (aexp_to_imported a1) (aexp_to_imported a2)
  | Original.LF_DOT_Imp.LF.Imp.BGt a1 a2 => Imported.Original_LF__DOT__Imp_LF_Imp_bexp_BGt (aexp_to_imported a1) (aexp_to_imported a2)
  | Original.LF_DOT_Imp.LF.Imp.BNot b1 => Imported.Original_LF__DOT__Imp_LF_Imp_bexp_BNot (bexp_to_imported b1)
  | Original.LF_DOT_Imp.LF.Imp.BAnd b1 b2 => Imported.Original_LF__DOT__Imp_LF_Imp_bexp_BAnd (bexp_to_imported b1) (bexp_to_imported b2)
  end.

Fixpoint imported_to_bexp (b : Imported.Original_LF__DOT__Imp_LF_Imp_bexp) : Original.LF_DOT_Imp.LF.Imp.bexp :=
  match b with
  | Imported.Original_LF__DOT__Imp_LF_Imp_bexp_BTrue => Original.LF_DOT_Imp.LF.Imp.BTrue
  | Imported.Original_LF__DOT__Imp_LF_Imp_bexp_BFalse => Original.LF_DOT_Imp.LF.Imp.BFalse
  | Imported.Original_LF__DOT__Imp_LF_Imp_bexp_BEq a1 a2 => Original.LF_DOT_Imp.LF.Imp.BEq (imported_to_aexp a1) (imported_to_aexp a2)
  | Imported.Original_LF__DOT__Imp_LF_Imp_bexp_BNeq a1 a2 => Original.LF_DOT_Imp.LF.Imp.BNeq (imported_to_aexp a1) (imported_to_aexp a2)
  | Imported.Original_LF__DOT__Imp_LF_Imp_bexp_BLe a1 a2 => Original.LF_DOT_Imp.LF.Imp.BLe (imported_to_aexp a1) (imported_to_aexp a2)
  | Imported.Original_LF__DOT__Imp_LF_Imp_bexp_BGt a1 a2 => Original.LF_DOT_Imp.LF.Imp.BGt (imported_to_aexp a1) (imported_to_aexp a2)
  | Imported.Original_LF__DOT__Imp_LF_Imp_bexp_BNot b1 => Original.LF_DOT_Imp.LF.Imp.BNot (imported_to_bexp b1)
  | Imported.Original_LF__DOT__Imp_LF_Imp_bexp_BAnd b1 b2 => Original.LF_DOT_Imp.LF.Imp.BAnd (imported_to_bexp b1) (imported_to_bexp b2)
  end.

Lemma bexp_roundtrip1 : forall b, imported_to_bexp (bexp_to_imported b) = b.
Proof.
  fix IH 1. intros b. destruct b; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal; apply aexp_roundtrip1.
  - f_equal; apply aexp_roundtrip1.
  - f_equal; apply aexp_roundtrip1.
  - f_equal; apply aexp_roundtrip1.
  - f_equal; apply IH.
  - f_equal; apply IH.
Qed.

Lemma bexp_roundtrip2 : forall b, bexp_to_imported (imported_to_bexp b) = b.
Proof.
  fix IH 1. intros b. destruct b; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal; apply aexp_roundtrip2.
  - f_equal; apply aexp_roundtrip2.
  - f_equal; apply aexp_roundtrip2.
  - f_equal; apply aexp_roundtrip2.
  - f_equal; apply IH.
  - f_equal; apply IH.
Qed.

Definition imported_Original_LF__DOT__Imp_LF_Imp_bexp : Type := Imported.Original_LF__DOT__Imp_LF_Imp_bexp.
Instance Original_LF__DOT__Imp_LF_Imp_bexp_iso : Iso Original.LF_DOT_Imp.LF.Imp.bexp imported_Original_LF__DOT__Imp_LF_Imp_bexp.
Proof.
  exists bexp_to_imported imported_to_bexp.
  - intro b. apply prop_to_sprop_eq_bexp. apply bexp_roundtrip2.
  - intro b. apply prop_to_sprop_eq_bexp. apply bexp_roundtrip1.
Defined.

Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.bexp := {}.
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_bexp := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.bexp Original_LF__DOT__Imp_LF_Imp_bexp_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.bexp Imported.Original_LF__DOT__Imp_LF_Imp_bexp Original_LF__DOT__Imp_LF_Imp_bexp_iso := {}.