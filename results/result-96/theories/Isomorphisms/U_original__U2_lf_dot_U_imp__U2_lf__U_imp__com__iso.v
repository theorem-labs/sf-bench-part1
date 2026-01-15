From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__bexp__iso.
From IsomorphismChecker Require Export Isomorphisms.U_string__string__iso.

Definition imported_Original_LF__DOT__Imp_LF_Imp_com : Type := Imported.Original_LF__DOT__Imp_LF_Imp_com.
Instance Original_LF__DOT__Imp_LF_Imp_com_iso : Iso Original.LF_DOT_Imp.LF.Imp.com imported_Original_LF__DOT__Imp_LF_Imp_com.
Admitted.
Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.com := {}.
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_com := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.com Original_LF__DOT__Imp_LF_Imp_com_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.com Imported.Original_LF__DOT__Imp_LF_Imp_com Original_LF__DOT__Imp_LF_Imp_com_iso := {}.
