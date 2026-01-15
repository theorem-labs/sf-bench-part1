From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)


From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_0 : imported_nat := Imported.zero_nat.
Instance _0_iso : rel_iso nat_iso O imported_0.
Proof.
  unfold imported_0.
  constructor.
  simpl.
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant O := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.zero_nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor O _0_iso := {}.
Instance: IsoStatementProofBetween O Imported.zero_nat _0_iso := {}.