From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_True : SProp := Imported.True.
Instance True_iso : (Iso Logic.True imported_True).
Proof.
  unshelve eapply Build_Iso.
  - (* to: True -> imported_True *)
    exact (fun _ => Imported.CoqTrue_I).
  - (* from: imported_True -> True *)
    exact (fun _ => I).
  - (* to_from: forall x, eq (to (from x)) x *)
    intro x. 
    (* In SProp, all inhabitants are equal by definition *)
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to: forall x, eq (from (to x)) x *)
    intro x.
    (* x : True (Prop), need to show eq I x *)
    destruct x.
    apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Logic.True := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.True := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Logic.True True_iso := {}.
Instance: IsoStatementProofBetween Logic.True Imported.True True_iso := {}.