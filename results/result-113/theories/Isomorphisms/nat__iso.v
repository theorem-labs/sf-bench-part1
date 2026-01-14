From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_nat : Type := Imported.nat.

(* Convert Coq nat to Imported.nat *)
Fixpoint nat_to_imported (n : nat) : Imported.nat :=
  match n with
  | O => Imported.nat_zero
  | S m => Imported.nat_succ (nat_to_imported m)
  end.

(* Convert Imported.nat to Coq nat *)
Fixpoint imported_to_nat (n : Imported.nat) : nat :=
  match n with
  | Imported.nat_zero => O
  | Imported.nat_succ m => S (imported_to_nat m)
  end.

Lemma nat_to_from : forall x : Imported.nat, IsomorphismDefinitions.eq (nat_to_imported (imported_to_nat x)) x.
Proof.
  fix IH 1.
  intros x.
  destruct x.
  - apply IsomorphismDefinitions.eq_refl.
  - simpl. apply IsoEq.f_equal. apply IH.
Qed.

Lemma nat_from_to : forall x : nat, IsomorphismDefinitions.eq (imported_to_nat (nat_to_imported x)) x.
Proof.
  fix IH 1.
  intros x.
  destruct x.
  - apply IsomorphismDefinitions.eq_refl.
  - simpl. apply IsoEq.f_equal. apply IH.
Qed.

Instance nat_iso : Iso nat imported_nat :=
  Build_Iso nat_to_imported imported_to_nat nat_to_from nat_from_to.

Instance: KnownConstant nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor nat nat_iso := {}.
Instance: IsoStatementProofBetween nat Imported.nat nat_iso := {}.