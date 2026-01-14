From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_nat : Type := Imported.nat.

(* Convert nat to Lean.Nat *)
Fixpoint nat_to_lean (n : Datatypes.nat) : Imported.nat :=
  match n with
  | O => Lean.Nat_zero
  | S n' => Lean.Nat_succ (nat_to_lean n')
  end.

(* Convert Lean.Nat to nat *)
Fixpoint lean_to_nat (n : Imported.nat) : Datatypes.nat :=
  match n with
  | Lean.Nat_zero => O
  | Lean.Nat_succ n' => S (lean_to_nat n')
  end.

Lemma nat_roundtrip1 : forall n : Datatypes.nat, IsomorphismDefinitions.eq (lean_to_nat (nat_to_lean n)) n.
Proof.
  fix IH 1.
  intros [|n']; simpl.
  - apply IsomorphismDefinitions.eq_refl.
  - apply IsoEq.f_equal. apply IH.
Qed.

Lemma nat_roundtrip2 : forall n : Imported.nat, IsomorphismDefinitions.eq (nat_to_lean (lean_to_nat n)) n.
Proof.
  fix IH 1.
  intros [|n']; simpl.
  - apply IsomorphismDefinitions.eq_refl.
  - apply IsoEq.f_equal. apply IH.
Qed.

Instance nat_iso : Iso Datatypes.nat imported_nat.
Proof.
  apply (Build_Iso (A:=Datatypes.nat) (B:=imported_nat) nat_to_lean lean_to_nat).
  - intro x. apply nat_roundtrip2.
  - intro x. apply nat_roundtrip1.
Defined.

Instance: KnownConstant Datatypes.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Datatypes.nat nat_iso := {}.
Instance: IsoStatementProofBetween Datatypes.nat Imported.nat nat_iso := {}.