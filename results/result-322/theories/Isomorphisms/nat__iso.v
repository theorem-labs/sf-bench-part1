From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

Definition imported_nat : Type := Imported.nat.

(* Define the mapping functions *)
Fixpoint nat_to_imported (n : nat) : imported_nat :=
  match n with
  | O => Imported.nat_O
  | S n' => Imported.nat_S (nat_to_imported n')
  end.

Fixpoint imported_to_nat (n : imported_nat) : nat :=
  match n with
  | Imported.nat_O => O
  | Imported.nat_S n' => S (imported_to_nat n')
  end.

Lemma nat_to_from : forall n : nat, IsomorphismDefinitions.eq (imported_to_nat (nat_to_imported n)) n.
Proof.
  induction n; simpl.
  - apply IsomorphismDefinitions.eq_refl.
  - apply (IsoEq.f_equal S IHn).
Qed.

Lemma nat_from_to : forall n : imported_nat, IsomorphismDefinitions.eq (nat_to_imported (imported_to_nat n)) n.
Proof.
  fix IH 1.
  intro n. destruct n as [|n']; simpl.
  - apply IsomorphismDefinitions.eq_refl.
  - apply (IsoEq.f_equal Imported.nat_S (IH n')).
Qed.

Instance nat_iso : Iso nat imported_nat.
Proof.
  unshelve eapply Build_Iso.
  - exact nat_to_imported.
  - exact imported_to_nat.
  - intro n. apply nat_from_to.
  - intro n. apply nat_to_from.
Defined.

Instance: KnownConstant nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor nat nat_iso := {}.
Instance: IsoStatementProofBetween nat Imported.nat nat_iso := {}.
