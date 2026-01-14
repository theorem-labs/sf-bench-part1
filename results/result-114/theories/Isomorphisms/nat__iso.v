From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

Definition imported_nat : Type := Imported.nat.

(* Lean.Nat is isomorphic to Coq's nat *)
Fixpoint nat_to_lean (n : nat) : Lean.Nat :=
  match n with
  | O => Lean.Nat_zero
  | S n' => Lean.Nat_succ (nat_to_lean n')
  end.

Fixpoint lean_to_nat (n : Lean.Nat) : nat :=
  match n with
  | Lean.Nat_zero => O
  | Lean.Nat_succ n' => S (lean_to_nat n')
  end.

Lemma nat_to_lean_from_sprop : forall n, IsomorphismDefinitions.eq (nat_to_lean (lean_to_nat n)) n.
Proof.
  fix IH 1.
  intro n. destruct n.
  - apply IsomorphismDefinitions.eq_refl.
  - simpl. apply f_equal. apply IH.
Qed.

Lemma lean_to_nat_from_sprop : forall n, IsomorphismDefinitions.eq (lean_to_nat (nat_to_lean n)) n.
Proof.
  fix IH 1.
  intro n. destruct n.
  - apply IsomorphismDefinitions.eq_refl.
  - simpl. apply f_equal. apply IH.
Qed.

Instance nat_iso : Iso nat imported_nat.
Proof.
  unfold imported_nat.
  exact (Build_Iso nat_to_lean lean_to_nat nat_to_lean_from_sprop lean_to_nat_from_sprop).
Defined.

Instance: KnownConstant nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor nat nat_iso := {}.
Instance: IsoStatementProofBetween nat Imported.nat nat_iso := {}.