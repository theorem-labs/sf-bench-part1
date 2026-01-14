From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.

(* Imported.True is in SProp (defined as PTrue) *)
Definition imported_True : SProp := Imported.True.

Instance True_iso : (Iso True imported_True).
Proof.
  unshelve eapply Build_Iso.
  - intro t. exact Imported.PTrue_intro.
  - intro s. exact Logic.I.
  - intro s. destruct s. apply IsomorphismDefinitions.eq_refl.
  - intro t. destruct t. apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant True := {}.
Instance: KnownConstant Imported.True := {}.
Instance: IsoStatementProofFor True True_iso := {}.
Instance: IsoStatementProofBetween True Imported.True True_iso := {}.