From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso. (* for speed *)

From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_S : imported_nat -> imported_nat := Imported.S.
Instance S_iso : forall (x1 : nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> rel_iso nat_iso (S x1) (imported_S x2).
Proof.
  intros x1 x2 Hrel.
  unfold rel_iso in *.
  unfold imported_S.
  simpl.
  apply (IsoEq.f_equal Imported.nat__S_).
  exact Hrel.
Defined.
Instance: KnownConstant S := {}.
Instance: KnownConstant Imported.S := {}.
Instance: IsoStatementProofFor S S_iso := {}.
Instance: IsoStatementProofBetween S Imported.S S_iso := {}.