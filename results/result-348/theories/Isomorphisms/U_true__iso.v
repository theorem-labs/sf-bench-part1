From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_True : SProp := Imported.True.

Definition True_to_imported (t : True) : imported_True := Imported.True__intro.
Definition imported_to_True (t : imported_True) : True := I.

Instance True_iso : (Iso True imported_True) := {|
  to := True_to_imported;
  from := imported_to_True;
  to_from := fun x => match x with Imported.True__intro => IsomorphismDefinitions.eq_refl end;
  from_to := fun x => match x with I => IsomorphismDefinitions.eq_refl end
|}.

Instance: KnownConstant True := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.True := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor True True_iso := {}.
Instance: IsoStatementProofBetween True Imported.True True_iso := {}.