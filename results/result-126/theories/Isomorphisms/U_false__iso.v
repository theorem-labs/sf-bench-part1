From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_False : SProp := Imported.False.

(* False is isomorphic to the imported False - both are empty types *)
(* Note: We define the functions using False_rect which handles empty types properly *)
Definition False_to_imported : False -> imported_False := 
  fun f => match f with end.

Definition imported_to_False : imported_False -> False :=
  fun f => match f : Imported.False with end.

Instance False_iso : (Iso False imported_False).
Proof.
  apply Build_Iso with (to := False_to_imported) (from := imported_to_False).
  - intros x. exact (match x : Imported.False with end).
  - intros x. destruct x.
Defined.

Instance: KnownConstant False := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.False := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor False False_iso := {}.
Instance: IsoStatementProofBetween False Imported.False False_iso := {}.