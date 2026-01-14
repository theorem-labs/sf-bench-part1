From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_True : SProp := Imported.True.

(* to_from: forall x : imported_True, eq (to (from x)) x
   from_to: forall x : True, eq (from (to x)) x *)
Instance True_iso : (Iso True imported_True).
Proof.
  refine (Build_Iso (fun _ => Imported.True_intro) (fun _ => I) _ _).
  - (* to_from: need IsomorphismDefinitions.eq in imported_True = SProp *)
    intro x. destruct x. apply IsomorphismDefinitions.eq_refl.
  - (* from_to: need IsomorphismDefinitions.eq in True *)
    intro x. destruct x. apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant True := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.True := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor True True_iso := {}.
Instance: IsoStatementProofBetween True Imported.True True_iso := {}.