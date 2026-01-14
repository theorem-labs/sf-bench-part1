From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso. (* for speed *)

Definition imported_nat : Type := Imported.nat_.
Instance nat_iso : Iso nat imported_nat.
Proof.
  exists (fix f (n : nat) : imported_nat :=
            match n with
            | O => Imported.nat__O_
            | S m => Imported.nat__S_ (f m)
            end)
         (fix g (n : imported_nat) : nat :=
            match n with
            | Imported.nat__O_ => O
            | Imported.nat__S_ m => S (g m)
            end).
  - fix IH 1. intros n.
    destruct n as [|m].
    + apply IsomorphismDefinitions.eq_refl.
    + simpl. apply (IsoEq.f_equal Imported.nat__S_). apply IH.
  - fix IH 1. intros [|m].
    + apply IsomorphismDefinitions.eq_refl.
    + simpl. apply (IsoEq.f_equal S). apply IH.
Defined.
Instance: KnownConstant nat := {}.
Instance: KnownConstant Imported.nat_ := {}.
Instance: IsoStatementProofFor nat nat_iso := {}.
Instance: IsoStatementProofBetween nat Imported.nat_ nat_iso := {}.