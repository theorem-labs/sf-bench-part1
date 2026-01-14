From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_bool : Type := Imported.Original_LF__DOT__Basics_LF_Basics_bool.
Instance Original_LF__DOT__Basics_LF_Basics_bool_iso : Iso Original.LF_DOT_Basics.LF.Basics.bool imported_Original_LF__DOT__Basics_LF_Basics_bool.
Admitted.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.bool := {}.
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_bool := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.bool Original_LF__DOT__Basics_LF_Basics_bool_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.bool Imported.Original_LF__DOT__Basics_LF_Basics_bool Original_LF__DOT__Basics_LF_Basics_bool_iso := {}.
