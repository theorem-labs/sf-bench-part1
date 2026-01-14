From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


(* Use standard library True - the isomorphism is identity *)
Definition imported_True : Type := True.
Instance True_iso : (Iso True imported_True) := iso_refl.
Instance: KnownConstant True := {}. 
Instance: IsoStatementProofFor True True_iso := {}.
Instance: IsoStatementProofBetween True True True_iso := {}.