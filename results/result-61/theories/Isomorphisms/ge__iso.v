From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.

From IsomorphismChecker Require Export Isomorphisms.le__iso.

Definition imported_ge : imported_nat -> imported_nat -> SProp := Imported.ge.

(* ge m n = le n m in both Coq and Lean *)
Instance ge_iso : forall (x1 : nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> forall (x3 : nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> Iso (x1 >= x3) (imported_ge x2 x4).
Proof.
  intros x1 x2 H12 x3 x4 H34.
  unfold imported_ge, Imported.ge.
  (* ge x1 x3 = le x3 x1, and Imported.ge x2 x4 = Imported.le x4 x2 *)
  unfold Peano.ge.
  apply (le_iso H34 H12).
Defined.

Instance: KnownConstant ge := {}. 
Instance: KnownConstant Imported.ge := {}. 
Instance: IsoStatementProofFor ge ge_iso := {}.
Instance: IsoStatementProofBetween ge Imported.ge ge_iso := {}.
