From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_nat : Type := Imported.nat.

Fixpoint nat_to (n : nat) : imported_nat :=
  match n with
  | O => Imported.nat_O
  | S m => Imported.nat_S (nat_to m)
  end.

Fixpoint nat_from (n : imported_nat) : nat :=
  match n with
  | Imported.nat_O => O
  | Imported.nat_S m => S (nat_from m)
  end.

Fixpoint nat_to_from (n : imported_nat) : IsomorphismDefinitions.eq (nat_to (nat_from n)) n :=
  match n with
  | Imported.nat_O => IsomorphismDefinitions.eq_refl
  | Imported.nat_S m => f_equal Imported.nat_S (nat_to_from m)
  end.

Fixpoint nat_from_to (n : nat) : IsomorphismDefinitions.eq (nat_from (nat_to n)) n :=
  match n with
  | O => IsomorphismDefinitions.eq_refl
  | S m => f_equal S (nat_from_to m)
  end.

Instance nat_iso : Iso nat imported_nat.
Proof.
  unshelve eapply Build_Iso.
  - exact nat_to.
  - exact nat_from.
  - exact nat_to_from.
  - exact nat_from_to.
Defined.
Instance: KnownConstant nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor nat nat_iso := {}.
Instance: IsoStatementProofBetween nat Imported.nat nat_iso := {}.