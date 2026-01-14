From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


Definition imported_False : SProp := Imported.False.
Instance False_iso : Iso False imported_False.
Admitted.
Instance: KnownConstant False := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.False := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor False False_iso := {}.
Instance: IsoStatementProofBetween False Imported.False False_iso := {}.