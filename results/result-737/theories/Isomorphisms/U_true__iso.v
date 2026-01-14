From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_True : SProp := Imported.True.

Instance True_iso : (Iso Logic.True imported_True).
Proof.
  unshelve eapply Build_Iso.
  + intro x. exact Imported.True_I.
  + intro x. exact Logic.I.
  + (* to_from: SProp has proof irrelevance built-in *)
    intro x. 
    (* x is in SProp, so all inhabitants are equal *)
    apply (Imported.True_indl (fun t => IsomorphismDefinitions.eq Imported.True_I t)).
    apply IsomorphismDefinitions.eq_refl.
  + intro x.
    destruct x.
    apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Logic.True := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.True := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Logic.True True_iso := {}.
Instance: IsoStatementProofBetween Logic.True Imported.True True_iso := {}.
