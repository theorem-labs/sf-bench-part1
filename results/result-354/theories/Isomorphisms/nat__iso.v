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
  - (* to *)
    fix to_f 1.
    intro n.
    destruct n as [|n'].
    + exact Imported.nat_O.
    + exact (Imported.nat_S (to_f n')).
  - (* from *)
    fix from_f 1.
    intro n.
    destruct n as [|n'].
    + exact O.
    + exact (S (from_f n')).
  - (* to_from *)
    fix IH 1.
    intro n. destruct n; simpl.
    + apply IsomorphismDefinitions.eq_refl.
    + apply IsoEq.f_equal. apply IH.
  - (* from_to *)
    fix IH 1.
    intro n. destruct n; simpl.
    + apply IsomorphismDefinitions.eq_refl.
    + apply IsoEq.f_equal. apply IH.
Defined.
Instance: KnownConstant nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor nat nat_iso := {}.
Instance: IsoStatementProofBetween nat Imported.nat nat_iso := {}.