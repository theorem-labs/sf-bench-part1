From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__bexp__iso.

Definition imported_Original_LF__DOT__Imp_LF_Imp_CIf : imported_Original_LF__DOT__Imp_LF_Imp_bexp -> imported_Original_LF__DOT__Imp_LF_Imp_com -> imported_Original_LF__DOT__Imp_LF_Imp_com -> imported_Original_LF__DOT__Imp_LF_Imp_com :=
  Imported.Original_LF__DOT__Imp_LF_Imp_com_CIf.

Instance Original_LF__DOT__Imp_LF_Imp_CIf_iso : forall (b : Original.LF_DOT_Imp.LF.Imp.bexp) (b' : imported_Original_LF__DOT__Imp_LF_Imp_bexp),
  rel_iso Original_LF__DOT__Imp_LF_Imp_bexp_iso b b' ->
  forall (c1 : Original.LF_DOT_Imp.LF.Imp.com) (c1' : imported_Original_LF__DOT__Imp_LF_Imp_com),
  rel_iso Original_LF__DOT__Imp_LF_Imp_com_iso c1 c1' ->
  forall (c2 : Original.LF_DOT_Imp.LF.Imp.com) (c2' : imported_Original_LF__DOT__Imp_LF_Imp_com),
  rel_iso Original_LF__DOT__Imp_LF_Imp_com_iso c2 c2' ->
  rel_iso Original_LF__DOT__Imp_LF_Imp_com_iso (Original.LF_DOT_Imp.LF.Imp.CIf b c1 c2) (imported_Original_LF__DOT__Imp_LF_Imp_CIf b' c1' c2').
Proof.
  intros b b' Hb c1 c1' Hc1 c2 c2' Hc2.
  unfold rel_iso in *; simpl in *.
  apply (f_equal3 Imported.Original_LF__DOT__Imp_LF_Imp_com_CIf Hb Hc1 Hc2).
Qed.

Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.CIf := {}.
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_com_CIf := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.CIf Original_LF__DOT__Imp_LF_Imp_CIf_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.CIf Imported.Original_LF__DOT__Imp_LF_Imp_com_CIf Original_LF__DOT__Imp_LF_Imp_CIf_iso := {}.
