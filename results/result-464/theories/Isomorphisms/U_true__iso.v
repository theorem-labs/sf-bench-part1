From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.

(* Imported.True is now SProp *)
Definition imported_True : SProp := Imported.True.

Instance True_iso : (Iso Logic.True imported_True).
Proof.
  unshelve eapply Build_Iso.
  - intro t. exact Imported.True_I.
  - intro s. exact Logic.I.
  - intro s. destruct s. apply IsomorphismDefinitions.eq_refl.
  - intro t. destruct t. apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Logic.True := {}.
Instance: KnownConstant Imported.True := {}.
Instance: IsoStatementProofFor Logic.True True_iso := {}.
Instance: IsoStatementProofBetween Logic.True Imported.True True_iso := {}.