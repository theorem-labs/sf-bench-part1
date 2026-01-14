From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_Original_False : SProp := Imported.Original_False.

(* Build an Iso between Original.False (Prop) and imported_Original_False (SProp) *)
Definition Original_False_to_imported : Original.False -> imported_Original_False := fun f => match f return imported_Original_False with end.
Definition imported_to_Original_False : imported_Original_False -> Original.False := fun f => Imported.False_recl (fun _ => Original.False) f.

Instance Original_False_iso : (Iso Original.False imported_Original_False).
Proof.
  refine {| to := Original_False_to_imported;
            from := imported_to_Original_False |}.
  - intro x. exact (Imported.False_indl (fun y => IsomorphismDefinitions.eq (Original_False_to_imported (imported_to_Original_False y)) y) x).
  - intro x. destruct x.
Defined.
Instance: KnownConstant Original.False := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_False := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.False Original_False_iso := {}.
Instance: IsoStatementProofBetween Original.False Imported.Original_False Original_False_iso := {}.