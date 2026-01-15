From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
(* Typeclasses Opaque rel_iso. *) (* for speed *)

Definition imported_True : SProp := Imported.MyTrue.
Instance True_iso : (Iso True imported_True).
Proof.
  apply Build_Iso with
    (to := fun _ => Imported.MyTrue_intro)
    (from := fun _ => I).
  - intro x. exact (Imported.MyTrue_indl (fun y => IsomorphismDefinitions.eq Imported.MyTrue_intro y) IsomorphismDefinitions.eq_refl x).
  - intro x. destruct x. apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant True := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.MyTrue := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor True True_iso := {}.
Instance: IsoStatementProofBetween True Imported.MyTrue True_iso := {}.