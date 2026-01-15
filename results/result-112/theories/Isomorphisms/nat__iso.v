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

Fixpoint imported_to_nat (n : imported_nat) : nat :=
  match n with
  | Imported.nat_O => O
  | Imported.nat_S n' => S (imported_to_nat n')
  end.

Lemma nat_roundtrip1 : forall n, imported_to_nat (nat_to_imported n) = n.
Proof. induction n; simpl; [reflexivity | f_equal; exact IHn]. Qed.

Lemma nat_roundtrip2 : forall n, nat_to_imported (imported_to_nat n) = n.
Proof. induction n; simpl; [reflexivity | f_equal; exact IHn]. Qed.

Instance nat_iso : Iso nat imported_nat.
Proof.
  refine {| to := nat_to_imported; from := imported_to_nat |}.
  - (* to_from: to (from x) = x for x : imported_nat *)
    intro x. 
    pose proof (nat_roundtrip2 x) as H.
    rewrite H. exact IsomorphismDefinitions.eq_refl.
  - (* from_to: from (to x) = x for x : nat *)
    intro x.
    pose proof (nat_roundtrip1 x) as H.
    rewrite H. exact IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor nat nat_iso := {}.
Instance: IsoStatementProofBetween nat Imported.nat nat_iso := {}.