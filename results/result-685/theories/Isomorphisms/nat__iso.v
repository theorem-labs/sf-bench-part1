From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_nat : Type := Imported.nat.

(* Helper functions for nat conversion *)
Fixpoint nat_to_imported (n : Datatypes.nat) : imported_nat :=
  match n with
  | O => Imported.nat_O
  | Datatypes.S n' => Imported.nat_S (nat_to_imported n')
  end.

Fixpoint nat_from_imported (n : imported_nat) : Datatypes.nat :=
  match n with
  | Imported.nat_O => O
  | Imported.nat_S n' => Datatypes.S (nat_from_imported n')
  end.

Lemma nat_from_to : forall n : Datatypes.nat, nat_from_imported (nat_to_imported n) = n.
Proof.
  intro n. induction n as [|n' IH].
  - reflexivity.
  - simpl. f_equal. exact IH.
Qed.

Lemma nat_to_from : forall n : imported_nat, nat_to_imported (nat_from_imported n) = n.
Proof.
  intro n. induction n as [|n' IH].
  - reflexivity.
  - simpl. f_equal. exact IH.
Qed.

Instance nat_iso : Iso nat imported_nat.
Proof.
  apply Build_Iso with
    (to := nat_to_imported)
    (from := nat_from_imported).
  - (* to_from *)
    intro n.
    induction n as [|n' IH].
    + apply IsomorphismDefinitions.eq_refl.
    + simpl. apply (IsoEq.f_equal Imported.nat_S IH).
  - (* from_to *)
    intro n.
    induction n as [|n' IH].
    + apply IsomorphismDefinitions.eq_refl.
    + simpl. apply (IsoEq.f_equal Datatypes.S IH).
Defined.
Instance: KnownConstant nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor nat nat_iso := {}.
Instance: IsoStatementProofBetween nat Imported.nat nat_iso := {}.