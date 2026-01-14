From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.

Definition imported_iff : SProp -> SProp -> SProp := Imported.iff.
Instance iff_iso : (forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : Prop) (x4 : SProp) (hx2 : Iso x3 x4), Iso (x1 <-> x3) (imported_iff x2 x4)).
Admitted.
Instance: KnownConstant iff := {}.
Instance: KnownConstant Imported.iff := {}.
Instance: IsoStatementProofFor iff iff_iso := {}.
Instance: IsoStatementProofBetween iff Imported.iff iff_iso := {}.
