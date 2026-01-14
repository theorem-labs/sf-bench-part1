From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_nat : Type := Imported.mynat.
Instance nat_iso : Iso nat imported_nat.
Proof.
  exists (fix f (n : nat) : imported_nat :=
            match n with
            | O => Imported.mynat_O
            | S m => Imported.mynat_S (f m)
            end)
         (fix g (n : imported_nat) : nat :=
            match n with
            | Imported.mynat_O => O
            | Imported.mynat_S m => S (g m)
            end).
  - fix IH 1. intros n.
    destruct n as [|m].
    + apply IsomorphismDefinitions.eq_refl.
    + simpl. apply (IsoEq.f_equal Imported.mynat_S). apply IH.
  - fix IH 1. intros [|m].
    + apply IsomorphismDefinitions.eq_refl.
    + simpl. apply (IsoEq.f_equal S). apply IH.
Defined.
Instance: KnownConstant nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.mynat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor nat nat_iso := {}.
Instance: IsoStatementProofBetween nat Imported.mynat nat_iso := {}.