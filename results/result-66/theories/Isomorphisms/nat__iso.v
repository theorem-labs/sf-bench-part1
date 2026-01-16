From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
(* Typeclasses Opaque rel_iso. *) (* for speed *)


Definition imported_nat : Type := Imported.nat.
Instance nat_iso : Iso nat imported_nat.
Proof.
  exists (fix f (n : nat) : imported_nat :=
            match n with
            | O => Imported.nat_O
            | S m => Imported.nat_S (f m)
            end)
         (fix g (n : imported_nat) : nat :=
            match n with
            | Imported.nat_O => O
            | Imported.nat_S m => S (g m)
            end).
  - fix IH 1. intros n.
    destruct n as [|m].
    + apply IsomorphismDefinitions.eq_refl.
    + simpl. apply (IsoEq.f_equal Imported.nat_S). apply IH.
  - fix IH 1. intros [|m].
    + apply IsomorphismDefinitions.eq_refl.
    + simpl. apply (IsoEq.f_equal S). apply IH.
Defined.
Instance: KnownConstant nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor nat nat_iso := {}.
Instance: IsoStatementProofBetween nat Imported.nat nat_iso := {}.
Definition nat_to_imported : nat -> imported_nat := to nat_iso.
Definition imported_to_nat : imported_nat -> nat := from nat_iso.

(* Helper lemmas for roundtripping *)
Lemma nat_roundtrip : forall n : nat, Logic.eq (imported_to_nat (nat_to_imported n)) n.
Proof.
  unfold imported_to_nat, nat_to_imported. simpl.
  fix IH 1.
  intros n. destruct n as [|m].
  - reflexivity.
  - simpl. apply Logic.f_equal. apply IH.
Defined.

Lemma imported_nat_roundtrip : forall n : imported_nat, Logic.eq (nat_to_imported (imported_to_nat n)) n.
Proof.
  unfold imported_to_nat, nat_to_imported. simpl.
  fix IH 1.
  intros n. destruct n as [|m].
  - reflexivity.
  - simpl. apply Logic.f_equal. apply IH.
Defined.

(* ISO versions of roundtrip lemmas *)
Lemma nat_from_to : forall n : nat, IsomorphismDefinitions.eq (imported_to_nat (nat_to_imported n)) n.
Proof.
  intros. apply seq_of_eq. apply nat_roundtrip.
Defined.

Lemma nat_to_from : forall n : imported_nat, IsomorphismDefinitions.eq (nat_to_imported (imported_to_nat n)) n.
Proof.
  intros. apply seq_of_eq. apply imported_nat_roundtrip.
Defined.
