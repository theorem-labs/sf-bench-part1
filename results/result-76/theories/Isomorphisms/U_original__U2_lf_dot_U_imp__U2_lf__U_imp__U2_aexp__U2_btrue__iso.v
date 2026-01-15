From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bexp__iso.

Monomorphic Definition imported_Original_LF__DOT__Imp_LF_Imp_AExp_BTrue : imported_Original_LF__DOT__Imp_LF_Imp_AExp_bexp := Imported.Original_LF__DOT__Imp_LF_Imp_AExp_BTrue.
Monomorphic Instance Original_LF__DOT__Imp_LF_Imp_AExp_BTrue_iso :
  rel_iso Original_LF__DOT__Imp_LF_Imp_AExp_bexp_iso Original.LF_DOT_Imp.LF.Imp.AExp.BTrue imported_Original_LF__DOT__Imp_LF_Imp_AExp_BTrue.
Proof.
  constructor. simpl.
  unfold imported_Original_LF__DOT__Imp_LF_Imp_AExp_BTrue, Imported.Original_LF__DOT__Imp_LF_Imp_AExp_BTrue.
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.AExp.BTrue := {}.
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_AExp_BTrue := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.AExp.BTrue Original_LF__DOT__Imp_LF_Imp_AExp_BTrue_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.AExp.BTrue Imported.Original_LF__DOT__Imp_LF_Imp_AExp_BTrue Original_LF__DOT__Imp_LF_Imp_AExp_BTrue_iso := {}.
