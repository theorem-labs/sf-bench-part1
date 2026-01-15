From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_nat : Type := Imported.nat.

Fixpoint nat_to_imported (n : nat) : imported_nat :=
  match n with
  | O => Imported.nat_O
  | S m => Imported.nat_S (nat_to_imported m)
  end.

Fixpoint nat_from_imported (n : imported_nat) : nat :=
  match n with
  | Imported.nat_O => O
  | Imported.nat_S m => S (nat_from_imported m)
  end.

Lemma nat_to_from : forall x : imported_nat, IsomorphismDefinitions.eq (nat_to_imported (nat_from_imported x)) x.
Proof.
  fix IH 1.
  intros x. destruct x.
  - apply IsomorphismDefinitions.eq_refl.
  - simpl. apply IsoEq.f_equal. apply IH.
Qed.

Lemma nat_from_to : forall x : nat, IsomorphismDefinitions.eq (nat_from_imported (nat_to_imported x)) x.
Proof.
  fix IH 1.
  intros x. destruct x.
  - apply IsomorphismDefinitions.eq_refl.
  - simpl. apply IsoEq.f_equal. apply IH.
Qed.

Instance nat_iso : Iso nat imported_nat :=
  Build_Iso nat_to_imported nat_from_imported nat_to_from nat_from_to.

Instance: KnownConstant nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor nat nat_iso := {}.
Instance: IsoStatementProofBetween nat Imported.nat nat_iso := {}.