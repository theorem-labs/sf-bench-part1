From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_nat : Type := Imported.nat.

Fixpoint nat_to_imported (n : nat) : Imported.nat :=
  match n with
  | O => Imported.nat_O
  | S n' => Imported.nat_S (nat_to_imported n')
  end.

Fixpoint imported_to_nat (n : Imported.nat) : nat :=
  match n with
  | Imported.nat_O => O
  | Imported.nat_S n' => S (imported_to_nat n')
  end.

Section Roundtrips.
Local Notation "x = y" := (Logic.eq x y).

Lemma nat_roundtrip1 : forall n, nat_to_imported (imported_to_nat n) = n.
Proof.
  fix IH 1.
  intros n; destruct n; simpl.
  - exact Logic.eq_refl.
  - exact (Logic.f_equal Imported.nat_S (IH n)).
Qed.

Lemma nat_roundtrip2 : forall n, imported_to_nat (nat_to_imported n) = n.
Proof.
  induction n; simpl.
  - exact Logic.eq_refl.
  - exact (Logic.f_equal S IHn).
Qed.
End Roundtrips.

Instance nat_iso : Iso nat imported_nat.
Proof.
  exact (Build_Iso nat_to_imported imported_to_nat
    (fun n => seq_of_eq (nat_roundtrip1 n))
    (fun n => seq_of_eq (nat_roundtrip2 n))).
Defined.
Instance: KnownConstant nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor nat nat_iso := {}.
Instance: IsoStatementProofBetween nat Imported.nat nat_iso := {}.