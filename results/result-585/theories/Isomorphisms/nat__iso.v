From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


(* Imported.nat is Lean.Nat, which is different from Datatypes.nat.
   We need to build an isomorphism between Datatypes.nat and Lean.Nat. *)
Definition imported_nat : Type := Imported.nat.
Instance nat_iso : Iso Datatypes.nat imported_nat.
Proof.
  unshelve eapply Build_Iso.
  - (* to: Datatypes.nat -> Lean.Nat *)
    exact (fix to_nat (n : Datatypes.nat) : Lean.Nat :=
      match n with
      | O => Lean.Nat_zero
      | Datatypes.S n' => Lean.Nat_succ (to_nat n')
      end).
  - (* from: Lean.Nat -> Datatypes.nat *)
    exact (fix from_nat (n : Lean.Nat) : Datatypes.nat :=
      match n with
      | Lean.Nat_zero => O
      | Lean.Nat_succ n' => Datatypes.S (from_nat n')
      end).
  - (* to_from *)
    intro n.
    induction n as [|n' IH].
    + apply IsomorphismDefinitions.eq_refl.
    + simpl.
      apply (IsoEq.f_equal Lean.Nat_succ IH).
  - (* from_to *)
    intro n.
    induction n as [|n' IH].
    + apply IsomorphismDefinitions.eq_refl.
    + simpl.
      apply (IsoEq.f_equal Datatypes.S IH).
Defined.
Instance: KnownConstant Datatypes.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Datatypes.nat nat_iso := {}.
Instance: IsoStatementProofBetween Datatypes.nat Imported.nat nat_iso := {}.