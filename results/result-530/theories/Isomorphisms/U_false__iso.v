From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_False : SProp := Imported.False.
Instance False_iso : (Iso Logic.False imported_False).
Proof.
  unshelve eapply Build_Iso.
  - (* to: False -> imported_False *)
    intro x. destruct x.
  - (* from: imported_False -> False *)
    intro x. destruct x.
  - (* to_from *)
    intro x. destruct x.
  - (* from_to *)
    intro x. destruct x.
Defined.

Instance: KnownConstant Logic.False := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.False := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Logic.False False_iso := {}.
Instance: IsoStatementProofBetween Logic.False Imported.False False_iso := {}.