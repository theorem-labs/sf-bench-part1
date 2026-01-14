From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


Definition imported_Original_LF__DOT__Imp_LF_Imp_bexp : Type := Imported.Original_LF__DOT__Imp_LF_Imp_bexp.
Instance Original_LF__DOT__Imp_LF_Imp_bexp_iso : Iso Original.LF_DOT_Imp.LF.Imp.bexp imported_Original_LF__DOT__Imp_LF_Imp_bexp.
Admitted.
Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.bexp := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_bexp := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.bexp Original_LF__DOT__Imp_LF_Imp_bexp_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.bexp Imported.Original_LF__DOT__Imp_LF_Imp_bexp Original_LF__DOT__Imp_LF_Imp_bexp_iso := {}.