From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_False : SProp := Imported.False.

Definition False_to_imported : Logic.False -> imported_False := fun f => match f return imported_False with end.
(* Use match on SProp False - since it has no constructors, the match is trivially total *)
Definition imported_to_False : imported_False -> Logic.False := 
  fun f => match f return Logic.False with end.

Instance False_iso : (Iso Logic.False imported_False).
Proof.
  refine {| to := False_to_imported;
            from := imported_to_False |}.
  - intro x. apply IsomorphismDefinitions.eq_refl.
  - intro x. destruct x.
Defined.
Instance: KnownConstant Logic.False := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.False := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Logic.False False_iso := {}.
Instance: IsoStatementProofBetween Logic.False Imported.False False_iso := {}.