From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
(* Typeclasses Opaque rel_iso. *) (* for speed *)


Definition imported_nat : Type := Imported.nat.

Fixpoint nat_to_imported (n : nat) : imported_nat :=
  match n with
  | O => Imported.nat_O
  | S m => Imported.nat_S (nat_to_imported m)
  end.

Fixpoint imported_to_nat (n : imported_nat) : nat :=
  match n with
  | Imported.nat_O => O
  | Imported.nat_S m => S (imported_to_nat m)
  end.

Instance nat_iso : Iso nat imported_nat.
Proof.
  exists nat_to_imported imported_to_nat.
  - fix IH 1. intros n.
    destruct n as [|m].
    + apply IsomorphismDefinitions.eq_refl.
    + simpl. apply (IsoEq.f_equal Imported.nat_S). apply IH.
  - fix IH 1. intros [|m].
    + apply IsomorphismDefinitions.eq_refl.
    + simpl. apply (IsoEq.f_equal S). apply IH.
Defined.

Lemma imported_round_trip : forall n, nat_to_imported (imported_to_nat n) = n.
Proof.
  fix IH 1. intros n.
  destruct n as [|m].
  - reflexivity.
  - simpl. f_equal. apply IH.
Qed.

Instance: KnownConstant nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor nat nat_iso := {}.
Instance: IsoStatementProofBetween nat Imported.nat nat_iso := {}.