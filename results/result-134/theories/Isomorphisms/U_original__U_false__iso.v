From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_Original_False : SProp := Imported.Original_False.

(* Original.False and Imported.Original_False are both empty types *)
Definition Original_False_to_imported (x : Original.False) : imported_Original_False := match x with end.
Definition imported_to_Original_False (x : imported_Original_False) : Original.False := match x with end.

Definition Original_False_to_from (x : imported_Original_False) : IsomorphismDefinitions.eq (Original_False_to_imported (imported_to_Original_False x)) x :=
  match x with end.

Definition Original_False_from_to (x : Original.False) : IsomorphismDefinitions.eq (imported_to_Original_False (Original_False_to_imported x)) x :=
  match x with end.

Instance Original_False_iso : (Iso Original.False imported_Original_False) :=
  Build_Iso Original_False_to_imported imported_to_Original_False Original_False_to_from Original_False_from_to.

Instance: KnownConstant Original.False := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_False := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.False Original_False_iso := {}.
Instance: IsoStatementProofBetween Original.False Imported.Original_False Original_False_iso := {}.