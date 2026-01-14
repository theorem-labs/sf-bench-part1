From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_True : SProp := Imported.True.
Instance True_iso : (Iso True imported_True).
Proof.
  unshelve eapply Build_Iso.
  - (* to: True -> imported_True *)
    intro H. exact Imported.True_intro.
  - (* from: imported_True -> True *)
    intro H. exact I.
  - (* to_from: forall x : imported_True, eq (to (from x)) x *)
    (* x is in SProp, so we can use proof irrelevance for SProp *)
    intro x. 
    (* Both to (from x) and x are in SProp, so they're equal *)
    exact IsomorphismDefinitions.eq_refl.
  - (* from_to: forall x : True, eq (from (to x)) x *)
    intro x. 
    (* x : True, from (to x) = I : True *)
    destruct x.
    exact IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant True := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.True := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor True True_iso := {}.
Instance: IsoStatementProofBetween True Imported.True True_iso := {}.
