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

Fixpoint imported_to_nat (n : Imported.nat) : nat :=
  match n with
  | Imported.nat_O => O
  | Imported.nat_S n' => S (imported_to_nat n')
  end.

Lemma nat_roundtrip1 : forall n, IsomorphismDefinitions.eq (imported_to_nat (nat_to_imported n)) n.
Proof.
  fix IH 1.
  intro n. destruct n as [|n']; simpl.
  - apply IsomorphismDefinitions.eq_refl.
  - apply (IsoEq.f_equal S). apply IH.
Defined.

Lemma nat_roundtrip2 : forall n, IsomorphismDefinitions.eq (nat_to_imported (imported_to_nat n)) n.
Proof.
  fix IH 1.
  intro n. destruct n as [|n']; simpl.
  - apply IsomorphismDefinitions.eq_refl.
  - apply (IsoEq.f_equal Imported.nat_S). apply IH.
Defined.

Instance nat_iso : Iso nat imported_nat.
Proof.
  exact (Build_Iso nat_to_imported imported_to_nat nat_roundtrip2 nat_roundtrip1).
Defined.

Instance: KnownConstant nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor nat nat_iso := {}.
Instance: IsoStatementProofBetween nat Imported.nat nat_iso := {}.