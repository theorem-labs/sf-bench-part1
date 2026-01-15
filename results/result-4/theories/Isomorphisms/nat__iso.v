From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.

Definition imported_nat : Type := Imported.nat.

(* Forward and backward conversions between nat and Imported.nat *)
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

Lemma nat_to_from : forall n : Imported.nat, Logic.eq (nat_to_imported (nat_from_imported n)) n.
Proof.
  fix IH 1.
  intros n. destruct n as [| n']; simpl.
  - reflexivity.
  - apply Logic.f_equal. apply IH.
Qed.

Lemma nat_from_to : forall n : nat, Logic.eq (nat_from_imported (nat_to_imported n)) n.
Proof.
  fix IH 1.
  intros n. destruct n as [| n']; simpl.
  - reflexivity.
  - apply Logic.f_equal. apply IH.
Qed.

Instance nat_iso : Iso nat imported_nat.
Proof.
  refine {|
    to := nat_to_imported;
    from := nat_from_imported;
    to_from := _;
    from_to := _
  |}.
  - intros n. apply seq_of_eq. apply nat_to_from.
  - intros n. apply seq_of_eq. apply nat_from_to.
Defined.

(* Aliases for compatibility *)
Definition imported_to_nat := nat_from_imported.
Definition nat_roundtrip1 := nat_from_to.
Definition nat_roundtrip2 := nat_to_from.

Instance: KnownConstant nat := {}.
Instance: KnownConstant Imported.nat := {}.
Instance: IsoStatementProofFor nat nat_iso := {}.
Instance: IsoStatementProofBetween nat Imported.nat nat_iso := {}.
