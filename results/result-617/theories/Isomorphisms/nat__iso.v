From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_nat : Type := Imported.nat.
Instance nat_iso : Iso nat imported_nat.
Proof.
  unshelve eapply Build_Iso.
  - (* to: nat -> Imported.nat *)
    exact (fix to_nat (n : nat) : imported_nat :=
      match n with
      | Datatypes.O => Imported.nat_O
      | Datatypes.S m => Imported.nat_S (to_nat m)
      end).
  - (* from: Imported.nat -> nat *)
    exact (fix from_nat (n : imported_nat) : nat :=
      match n with
      | Imported.nat_O => Datatypes.O
      | Imported.nat_S m => Datatypes.S (from_nat m)
      end).
  - (* to_from *)
    intro n.
    induction n as [|m IH].
    + apply IsomorphismDefinitions.eq_refl.
    + simpl. apply (IsoEq.f_equal Imported.nat_S IH).
  - (* from_to *)
    intro n.
    induction n as [|m IH].
    + apply IsomorphismDefinitions.eq_refl.
    + simpl. apply (IsoEq.f_equal Datatypes.S IH).
Defined.
Instance: KnownConstant nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor nat nat_iso := {}.
Instance: IsoStatementProofBetween nat Imported.nat nat_iso := {}.
