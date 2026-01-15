From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)


Definition imported_nat : Type := Imported.mynat.

Fixpoint nat_to_imported (n : nat) : Imported.mynat :=
  match n with
  | O => Imported.mynat_O
  | Datatypes.S m => Imported.mynat_S (nat_to_imported m)
  end.

Fixpoint nat_from_imported (n : Imported.mynat) : nat :=
  match n with
  | Imported.mynat_O => O
  | Imported.mynat_S m => Datatypes.S (nat_from_imported m)
  end.

Lemma from_to_nat : forall n, IsomorphismDefinitions.eq (nat_from_imported (nat_to_imported n)) n.
Proof.
  fix IH 1.
  intros n. destruct n as [|n'].
  - simpl. apply IsomorphismDefinitions.eq_refl.
  - simpl. apply (IsoEq.f_equal Datatypes.S). apply IH.
Defined.

Lemma to_from_nat : forall n, IsomorphismDefinitions.eq (nat_to_imported (nat_from_imported n)) n.
Proof.
  fix IH 1.
  intros n. destruct n as [|n'].
  - simpl. apply IsomorphismDefinitions.eq_refl.
  - simpl. apply (IsoEq.f_equal Imported.mynat_S). apply IH.
Defined.

Instance nat_iso : Iso nat imported_nat.
Proof.
  exists nat_to_imported nat_from_imported.
  - exact to_from_nat.
  - exact from_to_nat.
Defined.

Instance: KnownConstant nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.mynat := {}. (* only needed when rel_iso is typeclasses opaque *)