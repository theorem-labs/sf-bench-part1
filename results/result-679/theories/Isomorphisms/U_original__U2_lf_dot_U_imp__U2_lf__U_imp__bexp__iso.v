From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso.

Definition imported_Original_LF__DOT__Imp_LF_Imp_bexp : Type := Imported.Original_LF__DOT__Imp_LF_Imp_bexp.

Fixpoint bexp_to_imported (b : Original.LF_DOT_Imp.LF.Imp.bexp) : imported_Original_LF__DOT__Imp_LF_Imp_bexp :=
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

Fixpoint bexp_from_imported (b : imported_Original_LF__DOT__Imp_LF_Imp_bexp) : Original.LF_DOT_Imp.LF.Imp.bexp :=
  match b with
  | Imported.Original_LF__DOT__Imp_LF_Imp_bexp_BTrue => Original.LF_DOT_Imp.LF.Imp.BTrue
  | Imported.Original_LF__DOT__Imp_LF_Imp_bexp_BFalse => Original.LF_DOT_Imp.LF.Imp.BFalse
  | Imported.Original_LF__DOT__Imp_LF_Imp_bexp_BEq a1 a2 => Original.LF_DOT_Imp.LF.Imp.BEq (aexp_from_imported a1) (aexp_from_imported a2)
  | Imported.Original_LF__DOT__Imp_LF_Imp_bexp_BNeq a1 a2 => Original.LF_DOT_Imp.LF.Imp.BNeq (aexp_from_imported a1) (aexp_from_imported a2)
  | Imported.Original_LF__DOT__Imp_LF_Imp_bexp_BLe a1 a2 => Original.LF_DOT_Imp.LF.Imp.BLe (aexp_from_imported a1) (aexp_from_imported a2)
  | Imported.Original_LF__DOT__Imp_LF_Imp_bexp_BGt a1 a2 => Original.LF_DOT_Imp.LF.Imp.BGt (aexp_from_imported a1) (aexp_from_imported a2)
  | Imported.Original_LF__DOT__Imp_LF_Imp_bexp_BNot b1 => Original.LF_DOT_Imp.LF.Imp.BNot (bexp_from_imported b1)
  | Imported.Original_LF__DOT__Imp_LF_Imp_bexp_BAnd b1 b2 => Original.LF_DOT_Imp.LF.Imp.BAnd (bexp_from_imported b1) (bexp_from_imported b2)
  end.

Instance Original_LF__DOT__Imp_LF_Imp_bexp_iso : Iso Original.LF_DOT_Imp.LF.Imp.bexp imported_Original_LF__DOT__Imp_LF_Imp_bexp.
Proof.
  unshelve eapply Build_Iso.
  - exact bexp_to_imported.
  - exact bexp_from_imported.
  - fix to_from 1. intro b. destruct b; simpl.
    + apply IsomorphismDefinitions.eq_refl.
    + apply IsomorphismDefinitions.eq_refl.
    + apply (IsoEq.f_equal2 Imported.Original_LF__DOT__Imp_LF_Imp_bexp_BEq); apply (@IsomorphismDefinitions.to_from _ _ Original_LF__DOT__Imp_LF_Imp_aexp_iso).
    + apply (IsoEq.f_equal2 Imported.Original_LF__DOT__Imp_LF_Imp_bexp_BNeq); apply (@IsomorphismDefinitions.to_from _ _ Original_LF__DOT__Imp_LF_Imp_aexp_iso).
    + apply (IsoEq.f_equal2 Imported.Original_LF__DOT__Imp_LF_Imp_bexp_BLe); apply (@IsomorphismDefinitions.to_from _ _ Original_LF__DOT__Imp_LF_Imp_aexp_iso).
    + apply (IsoEq.f_equal2 Imported.Original_LF__DOT__Imp_LF_Imp_bexp_BGt); apply (@IsomorphismDefinitions.to_from _ _ Original_LF__DOT__Imp_LF_Imp_aexp_iso).
    + apply (IsoEq.f_equal Imported.Original_LF__DOT__Imp_LF_Imp_bexp_BNot). apply to_from.
    + apply (IsoEq.f_equal2 Imported.Original_LF__DOT__Imp_LF_Imp_bexp_BAnd); apply to_from.
  - fix from_to 1. intro b. destruct b; simpl.
    + apply IsomorphismDefinitions.eq_refl.
    + apply IsomorphismDefinitions.eq_refl.
    + apply (IsoEq.f_equal2 Original.LF_DOT_Imp.LF.Imp.BEq); apply (@IsomorphismDefinitions.from_to _ _ Original_LF__DOT__Imp_LF_Imp_aexp_iso).
    + apply (IsoEq.f_equal2 Original.LF_DOT_Imp.LF.Imp.BNeq); apply (@IsomorphismDefinitions.from_to _ _ Original_LF__DOT__Imp_LF_Imp_aexp_iso).
    + apply (IsoEq.f_equal2 Original.LF_DOT_Imp.LF.Imp.BLe); apply (@IsomorphismDefinitions.from_to _ _ Original_LF__DOT__Imp_LF_Imp_aexp_iso).
    + apply (IsoEq.f_equal2 Original.LF_DOT_Imp.LF.Imp.BGt); apply (@IsomorphismDefinitions.from_to _ _ Original_LF__DOT__Imp_LF_Imp_aexp_iso).
    + apply (IsoEq.f_equal Original.LF_DOT_Imp.LF.Imp.BNot). apply from_to.
    + apply (IsoEq.f_equal2 Original.LF_DOT_Imp.LF.Imp.BAnd); apply from_to.
Defined.

Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.bexp := {}.
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_bexp := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.bexp Original_LF__DOT__Imp_LF_Imp_bexp_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.bexp Imported.Original_LF__DOT__Imp_LF_Imp_bexp Original_LF__DOT__Imp_LF_Imp_bexp_iso := {}.