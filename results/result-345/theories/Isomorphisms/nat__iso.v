From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_nat : Type := Imported.nat.

Fixpoint nat_to (n : Datatypes.nat) : Imported.nat :=
  match n with
  | O => Imported.nat_O
  | S n' => Imported.nat_S (nat_to n')
  end.

Fixpoint nat_from (n : Imported.nat) : Datatypes.nat :=
  match n with
  | Imported.nat_O => O
  | Imported.nat_S n' => S (nat_from n')
  end.

Lemma nat_to_from : forall n, IsomorphismDefinitions.eq (nat_to (nat_from n)) n.
Proof.
  fix IH 1. intros [|n'].
  - apply IsomorphismDefinitions.eq_refl.
  - simpl. apply IsoEq.f_equal. apply IH.
Defined.

Lemma nat_from_to : forall n, IsomorphismDefinitions.eq (nat_from (nat_to n)) n.
Proof.
  fix IH 1. intros [|n'].
  - apply IsomorphismDefinitions.eq_refl.
  - simpl. apply IsoEq.f_equal. apply IH.
Defined.

Instance nat_iso : Iso Datatypes.nat imported_nat :=
  Build_Iso nat_to nat_from nat_to_from nat_from_to.

Instance: KnownConstant Datatypes.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Datatypes.nat nat_iso := {}.
Instance: IsoStatementProofBetween Datatypes.nat Imported.nat nat_iso := {}.