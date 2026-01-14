From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.

Definition imported_nat : Type := Imported.mynat.

Fixpoint nat_to_imported (n : nat) : Imported.mynat :=
  match n with
  | O => Imported.mynat_O
  | S n' => Imported.mynat_S (nat_to_imported n')
  end.

Fixpoint imported_to_nat (n : Imported.mynat) : nat :=
  match n with
  | Imported.mynat_O => O
  | Imported.mynat_S n' => S (imported_to_nat n')
  end.

Lemma nat_roundtrip1 : forall n, imported_to_nat (nat_to_imported n) = n.
Proof. induction n; simpl; [reflexivity | f_equal; apply IHn]. Qed.

Lemma nat_roundtrip2 : forall n, nat_to_imported (imported_to_nat n) = n.
Proof. induction n; simpl; [reflexivity | f_equal; apply IHn]. Qed.

Instance nat_iso : Iso nat imported_nat.
Proof.
  exists nat_to_imported imported_to_nat.
  - intro n. rewrite nat_roundtrip2. exact IsomorphismDefinitions.eq_refl.
  - intro n. rewrite nat_roundtrip1. exact IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant nat := {}.
Instance: KnownConstant Imported.mynat := {}.
Instance: IsoStatementProofFor nat nat_iso := {}.
Instance: IsoStatementProofBetween nat Imported.mynat nat_iso := {}.
