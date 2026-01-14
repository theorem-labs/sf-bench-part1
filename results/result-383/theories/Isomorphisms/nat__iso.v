From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_nat : Type := Imported.nat.

(* Define the conversion functions *)
Fixpoint nat_to_imported (n : nat) : Imported.nat :=
  match n with
  | O => Lean.Nat_zero
  | S n' => Lean.Nat_succ (nat_to_imported n')
  end.

Fixpoint imported_to_nat (n : Imported.nat) : nat :=
  match n with
  | Lean.Nat_zero => O
  | Lean.Nat_succ n' => S (imported_to_nat n')
  end.

(* Prove round-trip properties with standard equality *)
Fixpoint nat_round_trip (n : nat) : imported_to_nat (nat_to_imported n) = n :=
  match n with
  | O => Coq.Init.Logic.eq_refl
  | S n' => match nat_round_trip n' in (_ = m) return (S (imported_to_nat (nat_to_imported n')) = S m) with
            | Coq.Init.Logic.eq_refl => Coq.Init.Logic.eq_refl
            end
  end.

Fixpoint imported_round_trip (n : Imported.nat) : nat_to_imported (imported_to_nat n) = n :=
  match n with
  | Lean.Nat_zero => Coq.Init.Logic.eq_refl
  | Lean.Nat_succ n' => match imported_round_trip n' in (_ = m) return (Lean.Nat_succ (nat_to_imported (imported_to_nat n')) = Lean.Nat_succ m) with
                         | Coq.Init.Logic.eq_refl => Coq.Init.Logic.eq_refl
                         end
  end.

(* Build the isomorphism *)
Instance nat_iso : Iso nat imported_nat := {|
  to := nat_to_imported;
  from := imported_to_nat;
  to_from := fun n => seq_of_eq (imported_round_trip n);
  from_to := fun n => seq_of_eq (nat_round_trip n)
|}.

Instance: KnownConstant nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor nat nat_iso := {}.
Instance: IsoStatementProofBetween nat Imported.nat nat_iso := {}.