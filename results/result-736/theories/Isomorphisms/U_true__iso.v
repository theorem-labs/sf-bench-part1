From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.

(* Imported.MyTrue is now SProp (mapped from Lean's True) *)
Definition imported_True : SProp := Imported.MyTrue.

Instance True_iso : (Iso True imported_True).
Proof.
  unshelve eapply Build_Iso.
  - intro t. exact Imported.MyTrue_intro.
  - intro s. exact Logic.I.
  - intro s. destruct s. apply IsomorphismDefinitions.eq_refl.
  - intro t. destruct t. apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant True := {}.
Instance: KnownConstant Imported.MyTrue := {}.
Instance: IsoStatementProofFor True True_iso := {}.
Instance: IsoStatementProofBetween True Imported.MyTrue True_iso := {}.