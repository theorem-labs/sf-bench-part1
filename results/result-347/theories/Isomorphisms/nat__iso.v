From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_nat : Type := Imported.nat.

(* Convert nat to imported_nat *)
Fixpoint nat_to_imported (n : nat) : imported_nat :=
  match n with
  | O => Imported.nat_O
  | S n' => Imported.nat_S (nat_to_imported n')
  end.

(* Convert imported_nat to nat *)
Fixpoint nat_from_imported (n : imported_nat) : nat :=
  match n with
  | Imported.nat_O => O
  | Imported.nat_S n' => S (nat_from_imported n')
  end.

(* Proof that to_from is identity *)
Fixpoint nat_to_from (n : imported_nat) : IsomorphismDefinitions.eq (nat_to_imported (nat_from_imported n)) n :=
  match n with
  | Imported.nat_O => IsomorphismDefinitions.eq_refl
  | Imported.nat_S n' => IsoEq.f_equal Imported.nat_S (nat_to_from n')
  end.

(* Proof that from_to is identity *)
Fixpoint nat_from_to (n : nat) : IsomorphismDefinitions.eq (nat_from_imported (nat_to_imported n)) n :=
  match n with
  | O => IsomorphismDefinitions.eq_refl
  | S n' => IsoEq.f_equal S (nat_from_to n')
  end.

Instance nat_iso : Iso nat imported_nat := {|
  to := nat_to_imported;
  from := nat_from_imported;
  to_from := nat_to_from;
  from_to := nat_from_to;
|}.

Instance: KnownConstant nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor nat nat_iso := {}.
Instance: IsoStatementProofBetween nat Imported.nat nat_iso := {}.