From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_False : SProp := Imported.myFalse.

(* Helper: eliminate SProp False to SInhabited False *)
Definition from_imported_False_sinhabited (x : imported_False) : SInhabited False :=
  match x return SInhabited False with end.

(* For empty types isomorphism - using sinhabitant for SProp->Prop *)
Instance False_iso : (Iso False imported_False).
Proof.
  unshelve econstructor.
  - exact (fun f => match f with end).
  - exact (fun x => sinhabitant (from_imported_False_sinhabited x)).
  - (* to_from : forall x : imported_False, to (from x) = x *)
    intro x. apply IsomorphismDefinitions.eq_refl.
  - (* from_to : forall x : False, from (to x) = x *)
    intro x. exfalso. exact x.
Defined.
Instance: KnownConstant False := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.myFalse := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor False False_iso := {}.
Instance: IsoStatementProofBetween False Imported.myFalse False_iso := {}.