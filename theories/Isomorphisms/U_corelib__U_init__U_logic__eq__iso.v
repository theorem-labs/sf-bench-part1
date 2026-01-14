From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq : forall x : Type, x -> x -> SProp := (@Imported.Corelib_Init_Logic_eq).
Instance Corelib_Init_Logic_eq_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq x4 x6).
Admitted.
Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq) Corelib_Init_Logic_eq_iso := {}.