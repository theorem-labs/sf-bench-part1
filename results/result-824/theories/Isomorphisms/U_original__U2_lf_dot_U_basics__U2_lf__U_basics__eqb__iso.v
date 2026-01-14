From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.
From IsomorphismChecker Require Export Isomorphisms.nat__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_eqb := Imported.Original_LF__DOT__Basics_LF_Basics_eqb.
Instance Original_LF__DOT__Basics_LF_Basics_eqb_iso : forall x1 x2, rel_iso nat_iso x1 x2 -> forall x3 x4, rel_iso nat_iso x3 x4 -> rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso (Original.LF_DOT_Basics.LF.Basics.eqb x1 x3) (imported_Original_LF__DOT__Basics_LF_Basics_eqb x2 x4).
Admitted.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.eqb := {}.
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_eqb := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.eqb Original_LF__DOT__Basics_LF_Basics_eqb_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.eqb Imported.Original_LF__DOT__Basics_LF_Basics_eqb Original_LF__DOT__Basics_LF_Basics_eqb_iso := {}.
