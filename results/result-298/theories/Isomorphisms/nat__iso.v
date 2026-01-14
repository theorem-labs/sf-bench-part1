From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

(* Use qualified nat to avoid shadowing from Imported *)
Local Notation Nat := Corelib.Init.Datatypes.nat.

Definition imported_nat : Type := Imported.nat.

Fixpoint nat_to_imported (n : Nat) : imported_nat :=
  match n with
  | O => Imported.nat_O
  | Datatypes.S n' => Imported.nat_S (nat_to_imported n')
  end.

Fixpoint imported_to_nat (n : imported_nat) : Nat :=
  match n with
  | Imported.nat_O => O
  | Imported.nat_S n' => Datatypes.S (imported_to_nat n')
  end.

Lemma nat_to_from : forall x : imported_nat, IsomorphismDefinitions.eq (nat_to_imported (imported_to_nat x)) x.
Proof.
  fix IH 1.
  intros x. destruct x.
  - apply IsomorphismDefinitions.eq_refl.
  - simpl. apply IsoEq.f_equal. apply IH.
Defined.

Lemma nat_from_to : forall x : Nat, IsomorphismDefinitions.eq (imported_to_nat (nat_to_imported x)) x.
Proof.
  fix IH 1.
  intros x. destruct x.
  - apply IsomorphismDefinitions.eq_refl.
  - simpl. apply IsoEq.f_equal. apply IH.
Defined.

Instance nat_iso : Iso Nat imported_nat :=
  Build_Iso nat_to_imported imported_to_nat nat_to_from nat_from_to.

Instance: KnownConstant Corelib.Init.Datatypes.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Corelib.Init.Datatypes.nat nat_iso := {}.
Instance: IsoStatementProofBetween Corelib.Init.Datatypes.nat Imported.nat nat_iso := {}.