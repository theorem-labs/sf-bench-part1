From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_nat : Type := Imported.nat.

(* Build the isomorphism between nat and Imported.nat *)
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

Fixpoint to_from_proof (n : Imported.nat) : IsomorphismDefinitions.eq (nat_to_imported (imported_to_nat n)) n :=
  match n return IsomorphismDefinitions.eq (nat_to_imported (imported_to_nat n)) n with
  | Imported.nat_O => IsomorphismDefinitions.eq_refl
  | Imported.nat_S n' => f_equal Imported.nat_S (to_from_proof n')
  end.

Fixpoint from_to_proof (n : nat) : IsomorphismDefinitions.eq (imported_to_nat (nat_to_imported n)) n :=
  match n return IsomorphismDefinitions.eq (imported_to_nat (nat_to_imported n)) n with
  | O => IsomorphismDefinitions.eq_refl
  | S n' => f_equal S (from_to_proof n')
  end.

Instance nat_iso : Iso nat imported_nat :=
  @Build_Iso nat imported_nat nat_to_imported imported_to_nat to_from_proof from_to_proof.

Instance: KnownConstant nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor nat nat_iso := {}.
Instance: IsoStatementProofBetween nat Imported.nat nat_iso := {}.