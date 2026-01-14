From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_le : imported_nat -> imported_nat -> SProp := Imported.le.
Instance le_iso : (forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx2 : rel_iso nat_iso x3 x4), Iso (x1 <= x3) (imported_le x2 x4)).
Admitted.
Instance: KnownConstant le := {}.
Instance: KnownConstant Imported.le := {}.
Instance: IsoStatementProofFor le le_iso := {}.
Instance: IsoStatementProofBetween le Imported.le le_iso := {}.
