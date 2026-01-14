From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_nat : Type := Imported.nat.

(* Convert between Stdlib nat and Imported nat *)
Fixpoint nat_to_imported (n : nat) : Imported.nat :=
  match n with
  | O => Imported.nat_O
  | S m => Imported.nat_S (nat_to_imported m)
  end.

Fixpoint imported_to_nat (n : Imported.nat) : nat :=
  match n with
  | Imported.nat_O => O
  | Imported.nat_S m => S (imported_to_nat m)
  end.

Fixpoint nat_to_from (n : Imported.nat) : IsomorphismDefinitions.eq (nat_to_imported (imported_to_nat n)) n :=
  match n as n0 return IsomorphismDefinitions.eq (nat_to_imported (imported_to_nat n0)) n0 with
  | Imported.nat_O => IsomorphismDefinitions.eq_refl
  | Imported.nat_S m => 
    match nat_to_from m in IsomorphismDefinitions.eq _ m0 return
      IsomorphismDefinitions.eq (Imported.nat_S (nat_to_imported (imported_to_nat m))) (Imported.nat_S m0)
    with
    | IsomorphismDefinitions.eq_refl => IsomorphismDefinitions.eq_refl
    end
  end.

Fixpoint nat_from_to (n : Datatypes.nat) : IsomorphismDefinitions.eq (imported_to_nat (nat_to_imported n)) n :=
  match n as n0 return IsomorphismDefinitions.eq (imported_to_nat (nat_to_imported n0)) n0 with
  | O => IsomorphismDefinitions.eq_refl
  | S m =>
    match nat_from_to m in IsomorphismDefinitions.eq _ m0 return
      IsomorphismDefinitions.eq (S (imported_to_nat (nat_to_imported m))) (S m0)
    with
    | IsomorphismDefinitions.eq_refl => IsomorphismDefinitions.eq_refl
    end
  end.

Instance nat_iso : Iso nat imported_nat.
Proof.
  unshelve eapply Build_Iso.
  - exact nat_to_imported.
  - exact imported_to_nat.
  - exact nat_to_from.
  - exact nat_from_to.
Defined.

Instance: KnownConstant nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor nat nat_iso := {}.
Instance: IsoStatementProofBetween nat Imported.nat nat_iso := {}.