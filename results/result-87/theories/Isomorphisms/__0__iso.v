From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Monomorphic Definition imported_0 : imported_nat := Imported._0.
Monomorphic Instance _0_iso : rel_iso nat_iso 0 imported_0.
Admitted.
Instance: KnownConstant 0 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported._0 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor 0 _0_iso := {}.
Instance: IsoStatementProofBetween 0 Imported._0 _0_iso := {}.