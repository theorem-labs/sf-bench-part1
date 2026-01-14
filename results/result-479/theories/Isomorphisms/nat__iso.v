From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_nat : Type := Imported.nat.

(* Define conversion functions between nat and Imported.nat *)
Fixpoint nat_to_imported (n : nat) : Imported.nat :=
  match n with
  | O => Imported.nat_O
  | S n' => Imported.nat_S (nat_to_imported n')
  end.

Fixpoint nat_from_imported (n : Imported.nat) : nat :=
  match n with
  | Imported.nat_O => O
  | Imported.nat_S n' => S (nat_from_imported n')
  end.

Lemma nat_to_from : forall x : Imported.nat, IsomorphismDefinitions.eq (nat_to_imported (nat_from_imported x)) x.
Proof.
  fix IH 1.
  intros x.
  destruct x as [|n'].
  - apply IsomorphismDefinitions.eq_refl.
  - simpl. apply IsoEq.f_equal. apply IH.
Qed.

Lemma nat_from_to : forall x : nat, IsomorphismDefinitions.eq (nat_from_imported (nat_to_imported x)) x.
Proof.
  fix IH 1.
  intros x.
  destruct x as [|n'].
  - apply IsomorphismDefinitions.eq_refl.
  - simpl. apply IsoEq.f_equal. apply IH.
Qed.

Instance nat_iso : Iso nat imported_nat := {|
  to := nat_to_imported;
  from := nat_from_imported;
  to_from := nat_to_from;
  from_to := nat_from_to
|}.

Instance: KnownConstant nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor nat nat_iso := {}.
Instance: IsoStatementProofBetween nat Imported.nat nat_iso := {}.
