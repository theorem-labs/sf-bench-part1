From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso.

Definition imported_Original_LF__DOT__Imp_LF_Imp_CWhile := Imported.Original_LF__DOT__Imp_LF_Imp_CWhile.
Instance Original_LF__DOT__Imp_LF_Imp_CWhile_iso : forall x1 x2, rel_iso Original_LF__DOT__Imp_LF_Imp_com_iso x1 x2.
Admitted.
Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.CWhile := {}.
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_CWhile := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.CWhile Original_LF__DOT__Imp_LF_Imp_CWhile_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.CWhile Imported.Original_LF__DOT__Imp_LF_Imp_CWhile Original_LF__DOT__Imp_LF_Imp_CWhile_iso := {}.
