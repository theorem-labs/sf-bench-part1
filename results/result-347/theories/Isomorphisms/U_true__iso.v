From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

(* Imported.True is already in SProp (Prop from Lean gets imported as SProp) *)
Definition imported_True : SProp := Imported.True.

Instance True_iso : (Iso True imported_True).
Proof.
  unshelve eapply Build_Iso.
  - intro. exact Imported.True_intro.
  - intro. exact Logic.I.
  - (* to_from: SProp proof irrelevance *)
    intro x. 
    destruct x. apply IsomorphismDefinitions.eq_refl.
  - intro H. destruct H. apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant True := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.True := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor True True_iso := {}.
Instance: IsoStatementProofBetween True Imported.True True_iso := {}.