From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

(* Imported.False = Imported.Original_False (by definition) *)
Definition imported_False : SProp := Imported.False.

(* Build an Iso between False (Prop) and imported_False (SProp) *)
Definition False_to_imported : False -> imported_False := fun f => match f return imported_False with end.
(* Use Original_False_recl since False is a definition, not an inductive *)
Definition imported_to_False : imported_False -> False := fun f => Imported.Original_False_recl (fun _ => False) f.

Instance False_iso : (Iso False imported_False).
Proof.
  refine {| to := False_to_imported;
            from := imported_to_False |}.
  - intro x. exact (Imported.Original_False_indl (fun y => IsomorphismDefinitions.eq (False_to_imported (imported_to_False y)) y) x).
  - intro x. destruct x.
Defined.

Instance: KnownConstant False := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.False := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor False False_iso := {}.
Instance: IsoStatementProofBetween False Imported.False False_iso := {}.