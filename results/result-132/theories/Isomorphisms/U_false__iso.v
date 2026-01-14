From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_False : SProp := Imported.False.

(* False and Imported.False are both empty types, so we can map between them *)
Definition False_to_imported (x : False) : imported_False := match x with end.
Definition imported_to_False (x : imported_False) : False := match x with end.

(* Both round-trip proofs are trivially true because there are no inhabitants *)
Definition False_to_from (x : imported_False) : IsomorphismDefinitions.eq (False_to_imported (imported_to_False x)) x :=
  match x with end.

Definition False_from_to (x : False) : IsomorphismDefinitions.eq (imported_to_False (False_to_imported x)) x :=
  match x with end.

Instance False_iso : (Iso False imported_False) :=
  Build_Iso False_to_imported imported_to_False False_to_from False_from_to.

Instance: KnownConstant False := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.False := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor False False_iso := {}.
Instance: IsoStatementProofBetween False Imported.False False_iso := {}.
