From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

(* Imported.True is now our SProp True *)
Definition imported_True : SProp := Imported.True.

(* Iso between Prop True and SProp True *)
Instance True_iso : (Iso True imported_True).
Proof.
  unshelve eapply Build_Iso.
  - (* to: True -> imported_True (SProp) *)
    intro H. exact Imported.True_intro.
  - (* from: imported_True -> True *)
    intro H. exact Logic.I.
  - (* to_from: eq in SProp, so proof irrelevance applies automatically *)
    intro x.
    exact (IsomorphismDefinitions.eq_refl Imported.True_intro).
  - (* from_to *)
    intro x; destruct x; apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant True := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.True := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor True True_iso := {}.
Instance: IsoStatementProofBetween True Imported.True True_iso := {}.