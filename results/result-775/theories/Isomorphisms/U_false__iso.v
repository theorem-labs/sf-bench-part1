From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.

Definition imported_False : SProp := Imported.Original_False.

(* For empty types, we use the eliminators *)
Definition False_to_imported_False (x : False) : imported_False :=
  match x return imported_False with end.

Definition imported_False_to_False (x : imported_False) : False :=
  Imported.Original_False_recl (fun _ => False) x.

Instance False_iso : (Iso False imported_False).
Proof.
  exists False_to_imported_False imported_False_to_False.
  - intro x. exact (Imported.Original_False_indl (fun y => IsomorphismDefinitions.eq (False_to_imported_False (imported_False_to_False y)) y) x).
  - intro x. destruct x.
Defined.
Instance: KnownConstant False := {}.
Instance: KnownConstant Imported.Original_False := {}.
Instance: IsoStatementProofFor False False_iso := {}.
Instance: IsoStatementProofBetween False Imported.Original_False False_iso := {}.
