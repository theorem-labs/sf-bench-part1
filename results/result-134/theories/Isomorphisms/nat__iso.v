From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_nat : Type := Imported.nat.

Fixpoint nat_to_imported (n : nat) : imported_nat :=
  match n with
  | O => Imported.nat_O
  | S n' => Imported.nat_S (nat_to_imported n')
  end.

Fixpoint imported_to_nat (n : imported_nat) : nat :=
  match n with
  | Imported.nat_O => O
  | Imported.nat_S n' => S (imported_to_nat n')
  end.

(* Round-trip proofs using SProp equality *)
Fixpoint nat_to_from (n : imported_nat) : IsomorphismDefinitions.eq (nat_to_imported (imported_to_nat n)) n :=
  match n with
  | Imported.nat_O => IsomorphismDefinitions.eq_refl Imported.nat_O
  | Imported.nat_S n' =>
      match nat_to_from n' in IsomorphismDefinitions.eq _ x return IsomorphismDefinitions.eq (Imported.nat_S (nat_to_imported (imported_to_nat n'))) (Imported.nat_S x) with
      | IsomorphismDefinitions.eq_refl _ => IsomorphismDefinitions.eq_refl (Imported.nat_S (nat_to_imported (imported_to_nat n')))
      end
  end.

Fixpoint nat_from_to (n : nat) : IsomorphismDefinitions.eq (imported_to_nat (nat_to_imported n)) n :=
  match n with
  | O => IsomorphismDefinitions.eq_refl O
  | S n' =>
      match nat_from_to n' in IsomorphismDefinitions.eq _ x return IsomorphismDefinitions.eq (S (imported_to_nat (nat_to_imported n'))) (S x) with
      | IsomorphismDefinitions.eq_refl _ => IsomorphismDefinitions.eq_refl (S (imported_to_nat (nat_to_imported n')))
      end
  end.

Instance nat_iso : Iso nat imported_nat :=
  Build_Iso nat_to_imported imported_to_nat nat_to_from nat_from_to.

Instance: KnownConstant nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor nat nat_iso := {}.
Instance: IsoStatementProofBetween nat Imported.nat nat_iso := {}.