From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_false__iso.

Definition imported_Logic_not : forall _ : SProp, SProp := Imported.Logic_not.
Definition Logic_not_iso : forall (x1 : Prop) (x2 : SProp), Iso x1 x2 -> Iso (~ x1) (imported_Logic_not x2)
  := fun (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) => IsoArrow hx False_iso.
Instance: KnownConstant Logic.not := {}.
Instance: KnownConstant Imported.Logic_not := {}.
Instance: IsoStatementProofFor Logic.not Logic_not_iso := {}.
Instance: IsoStatementProofBetween Logic.not Imported.Logic_not Logic_not_iso := {}.
