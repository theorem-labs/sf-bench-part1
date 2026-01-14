From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_False : SProp := Imported.False_.

(* Since Imported.False_ is an empty SProp, we need special handling *)
Definition False_to_imported_False (f : False) : imported_False := match f with end.

(* For the reverse direction, we use the fact that SProp False_ can be eliminated into any SProp *)
Definition imported_False_to_SInhabited_False (f : imported_False) : SInhabited False :=
  match f with end.

Definition imported_False_to_False (f : imported_False) : False :=
  sinhabitant (imported_False_to_SInhabited_False f).

Instance False_iso : (Iso False imported_False).
Proof.
  exists False_to_imported_False imported_False_to_False.
  - intro x. destruct x.
  - intro x. destruct x.
Defined.
Instance: KnownConstant False := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.False_ := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor False False_iso := {}.
Instance: IsoStatementProofBetween False Imported.False_ False_iso := {}.