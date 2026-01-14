From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


Definition imported_ex : forall x : Type, (x -> SProp) -> SProp := Imported.ex.
Instance ex_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1 -> Prop) (x4 : x2 -> SProp), (forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 x5) (x4 x6)) -> Iso (exists y, x3 y) (imported_ex x4).
Admitted.
Instance: KnownConstant ex := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.ex := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor ex ex_iso := {}.
Instance: IsoStatementProofBetween ex Imported.ex ex_iso := {}.