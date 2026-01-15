From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__aexp__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bexp__iso.

Monomorphic Definition imported_Original_LF__DOT__Imp_LF_Imp_AExp_BLe : imported_Original_LF__DOT__Imp_LF_Imp_AExp_aexp -> imported_Original_LF__DOT__Imp_LF_Imp_AExp_aexp -> imported_Original_LF__DOT__Imp_LF_Imp_AExp_bexp := Imported.Original_LF__DOT__Imp_LF_Imp_AExp_BLe.
Monomorphic Instance Original_LF__DOT__Imp_LF_Imp_AExp_BLe_iso : forall (x1 : Original.LF_DOT_Imp.LF.Imp.AExp.aexp) (x2 : imported_Original_LF__DOT__Imp_LF_Imp_AExp_aexp),
  rel_iso Original_LF__DOT__Imp_LF_Imp_AExp_aexp_iso x1 x2 ->
  forall (x3 : Original.LF_DOT_Imp.LF.Imp.AExp.aexp) (x4 : imported_Original_LF__DOT__Imp_LF_Imp_AExp_aexp),
  rel_iso Original_LF__DOT__Imp_LF_Imp_AExp_aexp_iso x3 x4 ->
  rel_iso Original_LF__DOT__Imp_LF_Imp_AExp_bexp_iso (Original.LF_DOT_Imp.LF.Imp.AExp.BLe x1 x3) (imported_Original_LF__DOT__Imp_LF_Imp_AExp_BLe x2 x4).
Proof.
  intros x1 x2 H12 x3 x4 H34.
  constructor. simpl.
  destruct H12 as [H12]. destruct H34 as [H34]. simpl in *.
  unfold imported_Original_LF__DOT__Imp_LF_Imp_AExp_BLe, Imported.Original_LF__DOT__Imp_LF_Imp_AExp_BLe.
  apply (IsoEq.f_equal2 Imported.Original_LF__DOT__Imp_LF_Imp_AExp_bexp_BLe H12 H34).
Defined.
Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.AExp.BLe := {}.
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_AExp_BLe := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.AExp.BLe Original_LF__DOT__Imp_LF_Imp_AExp_BLe_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.AExp.BLe Imported.Original_LF__DOT__Imp_LF_Imp_AExp_BLe Original_LF__DOT__Imp_LF_Imp_AExp_BLe_iso := {}.
