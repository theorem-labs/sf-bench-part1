From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


Definition imported_prod : Type -> Type -> Type := Imported.prod.
Instance prod_iso : forall x1 x2 : Type, Iso x1 x2 -> forall x3 x4 : Type, Iso x3 x4 -> Iso (x1 * x3) (imported_prod x2 x4).
Admitted.
Instance: KnownConstant prod := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.prod := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor prod prod_iso := {}.
Instance: IsoStatementProofBetween prod Imported.prod prod_iso := {}.