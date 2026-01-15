From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


(* Imported.True is an SProp. Build isomorphism between Logic.True : Prop and Imported.True : SProp *)
Definition imported_True : SProp := Imported.True.
Instance True_iso : (Iso Logic.True imported_True) :=
  {| to := fun _ => Imported.True_intro;
     from := fun _ => Logic.I;
     to_from := fun _ => IsomorphismDefinitions.eq_refl;
     from_to := fun x => match x with Logic.I => IsomorphismDefinitions.eq_refl end
  |}.
Instance: KnownConstant Logic.True := {}. 
Instance: KnownConstant Imported.True := {}.
Instance: IsoStatementProofFor Logic.True True_iso := {}.
Instance: IsoStatementProofBetween Logic.True Imported.True True_iso := {}.