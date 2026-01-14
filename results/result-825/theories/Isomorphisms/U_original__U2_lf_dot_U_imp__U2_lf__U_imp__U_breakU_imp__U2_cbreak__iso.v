From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso. (* for speed *)

From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__com__iso.

Definition imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_CBreak : imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_com := Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_CBreak.

Instance Original_LF__DOT__Imp_LF_Imp_BreakImp_CBreak_iso : rel_iso Original_LF__DOT__Imp_LF_Imp_BreakImp_com_iso Original.LF_DOT_Imp.LF.Imp.BreakImp.CBreak imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_CBreak.
Proof.
  unfold imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_CBreak.
  unfold Original_LF__DOT__Imp_LF_Imp_BreakImp_com_iso.
  unfold imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_com.
  simpl.
  exact IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.BreakImp.CBreak := {}.
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_CBreak := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.BreakImp.CBreak Original_LF__DOT__Imp_LF_Imp_BreakImp_CBreak_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.BreakImp.CBreak Imported.Original_LF__DOT__Imp_LF_Imp_BreakImp_CBreak Original_LF__DOT__Imp_LF_Imp_BreakImp_CBreak_iso := {}.