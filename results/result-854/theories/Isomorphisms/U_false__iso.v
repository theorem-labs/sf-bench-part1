From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_False : SProp := Imported.MyFalse.

Definition False_to_imported (f : False) : imported_False := False_sind _ f.
Definition imported_to_False (f : imported_False) : False := Imported.MyFalse_recl (fun _ => False) f.

Instance False_iso : (Iso False imported_False).
Proof.
  exists False_to_imported imported_to_False.
  - intro x. apply IsomorphismDefinitions.eq_refl.
  - intro x. destruct x.
Defined.
Instance: KnownConstant False := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.MyFalse := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor False False_iso := {}.
Instance: IsoStatementProofBetween False Imported.MyFalse False_iso := {}.