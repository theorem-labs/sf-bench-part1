From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_Nat_add : imported_nat -> imported_nat -> imported_nat := Imported.nat_add.
Instance Nat_add_iso : forall (x1 : nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> forall (x3 : nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> rel_iso nat_iso (x1 + x3) (imported_Nat_add x2 x4).
Admitted.
Instance: KnownConstant Nat.add := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat_add := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Nat.add Nat_add_iso := {}.
Instance: IsoStatementProofBetween Nat.add Imported.nat_add Nat_add_iso := {}.