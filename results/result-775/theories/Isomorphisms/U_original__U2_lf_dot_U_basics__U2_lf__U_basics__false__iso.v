From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_false := Imported.Original_LF__DOT__Basics_LF_Basics_false.
Instance Original_LF__DOT__Basics_LF_Basics_false_iso : rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso Original.LF_DOT_Basics.LF.Basics.false imported_Original_LF__DOT__Basics_LF_Basics_false.
Admitted.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.false := {}.
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_false := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.false Original_LF__DOT__Basics_LF_Basics_false_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.false Imported.Original_LF__DOT__Basics_LF_Basics_false Original_LF__DOT__Basics_LF_Basics_false_iso := {}.
