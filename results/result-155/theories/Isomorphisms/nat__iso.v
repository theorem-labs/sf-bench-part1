From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_nat : Type := Imported.nat.

Definition nat_to_imported : nat -> imported_nat :=
  fix f (n : nat) : imported_nat :=
    match n with
    | O => Imported.nat_O
    | Datatypes.S m => Imported.nat_S (f m)
    end.

Definition imported_to_nat : imported_nat -> nat :=
  fix g (n : imported_nat) : nat :=
    match n with
    | Imported.nat_O => O
    | Imported.nat_S m => Datatypes.S (g m)
    end.

Lemma nat_round_trip : forall n : nat, Logic.eq (imported_to_nat (nat_to_imported n)) n.
Proof.
  fix IH 1.
  intro n.
  destruct n as [|m].
  - reflexivity.
  - simpl. f_equal. apply IH.
Qed.

Lemma imported_round_trip : forall n : imported_nat, Logic.eq (nat_to_imported (imported_to_nat n)) n.
Proof.
  fix IH 1.
  intro n.
  destruct n as [|m].
  - reflexivity.
  - simpl. f_equal. apply IH.
Qed.

Instance nat_iso : Iso nat imported_nat.
Proof.
  exists nat_to_imported imported_to_nat.
  - fix IH 1. intros n.
    destruct n as [|m].
    + apply IsomorphismDefinitions.eq_refl.
    + simpl. apply (IsoEq.f_equal Imported.nat_S). apply IH.
  - fix IH 1. intros [|m].
    + apply IsomorphismDefinitions.eq_refl.
    + simpl. apply (IsoEq.f_equal Datatypes.S). apply IH.
Defined.
Instance: KnownConstant nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor nat nat_iso := {}.
Instance: IsoStatementProofBetween nat Imported.nat nat_iso := {}.
