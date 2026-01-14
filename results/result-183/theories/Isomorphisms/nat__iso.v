From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_nat : Type := Imported.nat.

Definition nat_to_imported (n : nat) : imported_nat :=
  nat_rect (fun _ => imported_nat) Imported.nat_O (fun _ ih => Imported.nat_S ih) n.

Definition imported_to_nat (n : imported_nat) : nat :=
  Imported.nat_rect (fun _ => nat) O (fun _ ih => Datatypes.S ih) n.

Lemma nat_to_from : forall x : imported_nat, IsomorphismDefinitions.eq (nat_to_imported (imported_to_nat x)) x.
Proof.
  unfold nat_to_imported, imported_to_nat.
  fix IH 1.
  intros x. destruct x.
  - apply IsomorphismDefinitions.eq_refl.
  - simpl. apply IsoEq.f_equal. apply IH.
Defined.

Lemma nat_from_to : forall x : nat, IsomorphismDefinitions.eq (imported_to_nat (nat_to_imported x)) x.
Proof.
  unfold nat_to_imported, imported_to_nat.
  fix IH 1.
  intros x. destruct x.
  - apply IsomorphismDefinitions.eq_refl.
  - simpl. apply IsoEq.f_equal. apply IH.
Defined.

Instance nat_iso : Iso nat imported_nat :=
  Build_Iso nat_to_imported imported_to_nat nat_to_from nat_from_to.

Instance: KnownConstant nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor nat nat_iso := {}.
Instance: IsoStatementProofBetween nat Imported.nat nat_iso := {}.