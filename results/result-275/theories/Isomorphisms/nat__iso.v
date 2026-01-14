From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_nat : Type := Imported.nat.

(* Convert nat to imported_nat *)
Fixpoint nat_to_imported (n : nat) : imported_nat :=
  match n with
  | O => Imported.nat_zero
  | S n' => Imported.nat_succ (nat_to_imported n')
  end.

(* Convert imported_nat to nat *)
Fixpoint imported_to_nat (n : imported_nat) : nat :=
  match n with
  | Imported.nat_zero => O
  | Imported.nat_succ n' => S (imported_to_nat n')
  end.

(* to_from: forall x : imported_nat, eq (nat_to_imported (imported_to_nat x)) x *)
Lemma to_from_nat : forall n : imported_nat, 
  IsomorphismDefinitions.eq (nat_to_imported (imported_to_nat n)) n.
Proof.
  fix IH 1.
  intro n. destruct n.
  - apply IsomorphismDefinitions.eq_refl.
  - simpl. apply IsoEq.f_equal. apply IH.
Qed.

(* from_to: forall x : nat, eq (imported_to_nat (nat_to_imported x)) x *)
Lemma from_to_nat : forall n : nat, 
  IsomorphismDefinitions.eq (imported_to_nat (nat_to_imported n)) n.
Proof.
  fix IH 1.
  intro n. destruct n.
  - apply IsomorphismDefinitions.eq_refl.
  - simpl. apply IsoEq.f_equal. apply IH.
Qed.

Instance nat_iso : Iso nat imported_nat.
Proof.
  refine (Build_Iso nat_to_imported imported_to_nat _ _).
  - intro n. apply to_from_nat.
  - intro n. apply from_to_nat.
Defined.
Instance: KnownConstant nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor nat nat_iso := {}.
Instance: IsoStatementProofBetween nat Imported.nat nat_iso := {}.