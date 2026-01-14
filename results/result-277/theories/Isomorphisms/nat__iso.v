From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_nat : Type := Imported.nat.

(* Conversion functions *)
Fixpoint nat_to_imported (n : Datatypes.nat) : imported_nat :=
  match n with
  | Datatypes.O => Imported.nat_O
  | Datatypes.S n' => Imported.nat_S (nat_to_imported n')
  end.

Fixpoint imported_to_nat (n : imported_nat) : Datatypes.nat :=
  match n with
  | Imported.nat_O => Datatypes.O
  | Imported.nat_S n' => Datatypes.S (imported_to_nat n')
  end.

Lemma nat_to_from : forall n : imported_nat, IsomorphismDefinitions.eq (nat_to_imported (imported_to_nat n)) n.
Proof.
  intro n.
  induction n as [|n' IH].
  - apply IsomorphismDefinitions.eq_refl.
  - simpl. apply IsoEq.f_equal. exact IH.
Qed.

Lemma nat_from_to : forall n : Datatypes.nat, IsomorphismDefinitions.eq (imported_to_nat (nat_to_imported n)) n.
Proof.
  intro n.
  induction n as [|n' IH].
  - apply IsomorphismDefinitions.eq_refl.
  - simpl. apply IsoEq.f_equal. exact IH.
Qed.

Instance nat_iso : Iso Datatypes.nat imported_nat :=
  Build_Iso nat_to_imported imported_to_nat nat_to_from nat_from_to.

Instance: KnownConstant Datatypes.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Datatypes.nat nat_iso := {}.
Instance: IsoStatementProofBetween Datatypes.nat Imported.nat nat_iso := {}.