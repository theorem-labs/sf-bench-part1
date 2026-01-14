From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


Definition imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist : Type := Imported.Original_LF__DOT__Lists_LF_Lists_NatList_natlist.
Instance Original_LF__DOT__Lists_LF_Lists_NatList_natlist_iso : Iso Original.LF_DOT_Lists.LF.Lists.NatList.natlist imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist.
Admitted.
Instance: KnownConstant Original.LF_DOT_Lists.LF.Lists.NatList.natlist := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Lists_LF_Lists_NatList_natlist := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.natlist Original_LF__DOT__Lists_LF_Lists_NatList_natlist_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.natlist Imported.Original_LF__DOT__Lists_LF_Lists_NatList_natlist Original_LF__DOT__Lists_LF_Lists_NatList_natlist_iso := {}.