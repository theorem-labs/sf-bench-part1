From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
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

Fixpoint nat_from_imported (n : imported_nat) : nat :=
  match n with
  | Imported.nat_O => O
  | Imported.nat_S n' => S (nat_from_imported n')
  end.

Instance nat_iso : Iso nat imported_nat.
Proof.
  unshelve eapply Build_Iso.
  - exact nat_to_imported.
  - exact nat_from_imported.
  - intro n.
    induction n as [|n' IH].
    + apply IsomorphismDefinitions.eq_refl.
    + simpl. apply IsoEq.f_equal. exact IH.
  - intro n.
    induction n as [|n' IH].
    + apply IsomorphismDefinitions.eq_refl.
    + simpl. apply IsoEq.f_equal. exact IH.
Defined.
Instance: KnownConstant nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor nat nat_iso := {}.
Instance: IsoStatementProofBetween nat Imported.nat nat_iso := {}.