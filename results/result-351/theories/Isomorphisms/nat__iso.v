From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_nat : Type := Imported.nat.

Fixpoint nat_to_imported (n : nat) : Imported.nat :=
  match n with
  | O => Imported.nat_O
  | S n' => Imported.nat_S (nat_to_imported n')
  end.

Fixpoint nat_from_imported (n : Imported.nat) : nat :=
  match n with
  | Imported.nat_O => O
  | Imported.nat_S n' => S (nat_from_imported n')
  end.

Lemma nat_to_from : forall n, IsomorphismDefinitions.eq (nat_to_imported (nat_from_imported n)) n.
Proof.
  fix IH 1.
  intro n. destruct n.
  - apply IsomorphismDefinitions.eq_refl.
  - simpl. apply (f_equal Imported.nat_S). apply IH.
Qed.

Lemma nat_from_to : forall n, IsomorphismDefinitions.eq (nat_from_imported (nat_to_imported n)) n.
Proof.
  fix IH 1.
  intro n. destruct n.
  - apply IsomorphismDefinitions.eq_refl.
  - simpl. apply (f_equal S). apply IH.
Qed.

Instance nat_iso : Iso nat imported_nat.
Proof.
  unshelve eapply Build_Iso.
  - exact nat_to_imported.
  - exact nat_from_imported.
  - exact nat_to_from.
  - exact nat_from_to.
Defined.
Instance: KnownConstant nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor nat nat_iso := {}.
Instance: IsoStatementProofBetween nat Imported.nat nat_iso := {}.
