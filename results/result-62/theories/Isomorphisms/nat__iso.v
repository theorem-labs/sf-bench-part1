From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)


Definition imported_nat : Type := Imported.nat.

Fixpoint nat_to_imported (n : nat) : imported_nat :=
  match n with
  | O => Imported.nat_O
  | S m => Imported.nat_S (nat_to_imported m)
  end.

Fixpoint imported_to_nat (n : imported_nat) : nat :=
  match n with
  | Imported.nat_O => O
  | Imported.nat_S m => S (imported_to_nat m)
  end.

Lemma nat_to_from : forall n, IsomorphismDefinitions.eq (nat_to_imported (imported_to_nat n)) n.
Proof.
  fix IH 1. intros n.
  destruct n as [|m].
  - apply IsomorphismDefinitions.eq_refl.
  - simpl. apply (IsoEq.f_equal Imported.nat_S). apply IH.
Qed.

Lemma nat_from_to : forall n, IsomorphismDefinitions.eq (imported_to_nat (nat_to_imported n)) n.
Proof.
  fix IH 1. intros [|m].
  - apply IsomorphismDefinitions.eq_refl.
  - simpl. apply (IsoEq.f_equal S). apply IH.
Qed.

(* Coq logic eq versions for easier use *)
Lemma nat_roundtrip1 : forall n, imported_to_nat (nat_to_imported n) = n.
Proof.
  induction n; simpl.
  - reflexivity.
  - f_equal. apply IHn.
Qed.

Lemma nat_roundtrip2 : forall n, nat_to_imported (imported_to_nat n) = n.
Proof.
  induction n; simpl.
  - reflexivity.
  - f_equal. apply IHn.
Qed.

Instance nat_iso : Iso nat imported_nat :=
  {| to := nat_to_imported; from := imported_to_nat; to_from := nat_to_from; from_to := nat_from_to |}.
Instance: KnownConstant nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor nat nat_iso := {}.
Instance: IsoStatementProofBetween nat Imported.nat nat_iso := {}.