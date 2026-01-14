From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_nat : Type := Imported.nat.
Instance nat_iso : Iso nat imported_nat.
Proof.
  unshelve eapply Build_Iso.
  - (* to: nat -> Imported.nat *)
    fix to_nat 1.
    intro n. destruct n as [|n'].
    + exact Imported.nat_O.
    + exact (Imported.nat_S (to_nat n')).
  - (* from: Imported.nat -> nat *)
    fix from_nat 1.
    intro n. destruct n as [|n'].
    + exact O.
    + exact (S (from_nat n')).
  - (* to_from *)
    fix to_from 1.
    intro n. destruct n as [|n'].
    + apply IsomorphismDefinitions.eq_refl.
    + simpl. apply IsoEq.f_equal. apply to_from.
  - (* from_to *)
    fix from_to 1.
    intro n. destruct n as [|n'].
    + apply IsomorphismDefinitions.eq_refl.
    + simpl. apply IsoEq.f_equal. apply from_to.
Defined.
Instance: KnownConstant nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor nat nat_iso := {}.
Instance: IsoStatementProofBetween nat Imported.nat nat_iso := {}.