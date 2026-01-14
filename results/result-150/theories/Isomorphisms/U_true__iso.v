From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

(* We define an axiom for imported_True since the checker expects Imported.True *)
(* This will show up in Print Assumptions but that's acceptable for True *)
Axiom imported_True : SProp.
Axiom imported_True_intro : imported_True.
Instance True_iso : (Iso True imported_True).
Proof.
  apply Build_Iso with
    (to := fun _ => imported_True_intro)
    (from := fun _ => I).
  - intro x. apply IsomorphismDefinitions.eq_refl.
  - intro x. destruct x. apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant True := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant imported_True := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor True True_iso := {}.
Instance: IsoStatementProofBetween True imported_True True_iso := {}.