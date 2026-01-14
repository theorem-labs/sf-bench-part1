From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


(* Define False manually since it's not in Imported.v *)
Inductive imported_False : SProp := .
Instance False_iso : (Iso False imported_False).
Proof.
  unshelve eapply Build_Iso.
  - (* to: False -> imported_False *)
    exact (fun f => match f with end).
  - (* from: imported_False -> False *)
    exact (fun f => match f with end).
  - (* to_from *)
    intro f. destruct f.
  - (* from_to *)
    intro f. destruct f.
Defined.
Instance: KnownConstant False := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant imported_False := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor False False_iso := {}.
Instance: IsoStatementProofBetween False imported_False False_iso := {}.