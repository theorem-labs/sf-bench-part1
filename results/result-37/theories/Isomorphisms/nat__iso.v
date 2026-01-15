From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)


Definition imported_nat : Type := Imported.nat.

(* Conversion function from nat to imported_nat *)
Fixpoint nat_to_imported (n : nat) : imported_nat :=
  match n with
  | O => Imported.nat_O
  | S m => Imported.nat_S (nat_to_imported m)
  end.

(* Conversion function from imported_nat to nat *)
Fixpoint imported_to_nat (n : imported_nat) : nat :=
  match n with
  | Imported.nat_O => O
  | Imported.nat_S m => S (imported_to_nat m)
  end.

(* Roundtrip lemmas *)
Lemma imported_nat_roundtrip : forall n : imported_nat, nat_to_imported (imported_to_nat n) = n.
Proof.
  fix IH 1. intros n. destruct n as [|m].
  - reflexivity.
  - simpl. apply (Logic.f_equal Imported.nat_S). apply IH.
Qed.

Lemma nat_roundtrip : forall n : nat, imported_to_nat (nat_to_imported n) = n.
Proof.
  fix IH 1. intros n. destruct n as [|m].
  - reflexivity.
  - simpl. apply (Logic.f_equal S). apply IH.
Qed.

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