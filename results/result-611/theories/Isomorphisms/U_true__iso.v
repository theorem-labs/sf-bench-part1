From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


(* Use Imported.True from the Lean export *)
Definition imported_True : SProp := Imported.True.
Instance True_iso : (Iso True imported_True).
Proof.
  unshelve eapply Build_Iso.
  - intro t. exact Imported.True_intro.
  - intro t. exact I.
  - intro t. apply IsomorphismDefinitions.eq_refl.
  - intro t. destruct t. apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant True := {}. 
Instance: KnownConstant Imported.True := {}. 
Instance: IsoStatementProofFor True True_iso := {}.
Instance: IsoStatementProofBetween True Imported.True True_iso := {}.