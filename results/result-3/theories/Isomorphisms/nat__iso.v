From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
(* Typeclasses Opaque rel_iso. *) (* for speed - disabled due to compatibility issues *)


Definition imported_nat : Type := Imported.nat.

(* Convert from standard nat to imported nat *)
Fixpoint nat_to_imported (n : Datatypes.nat) : Imported.nat :=
  match n with
  | Datatypes.O => Imported.nat_O
  | Datatypes.S m => Imported.nat_S (nat_to_imported m)
  end.

(* Convert from imported nat to standard nat *)
Fixpoint imported_to_nat (n : Imported.nat) : Datatypes.nat :=
  match n with
  | Imported.nat_O => Datatypes.O
  | Imported.nat_S m => Datatypes.S (imported_to_nat m)
  end.

Lemma nat_roundtrip1 : forall n, imported_to_nat (nat_to_imported n) = n.
Proof.
  intro n. induction n as [|n IHn].
  - reflexivity.
  - simpl. f_equal. exact IHn.
Qed.

Lemma nat_roundtrip2 : forall n, nat_to_imported (imported_to_nat n) = n.
Proof.
  intro n. induction n as [|n IHn].
  - reflexivity.
  - simpl. f_equal. exact IHn.
Qed.

(* Congruence lemmas for IsomorphismDefinitions.eq *)
Lemma natS_cong : forall x y : Imported.nat, 
  IsomorphismDefinitions.eq x y -> 
  IsomorphismDefinitions.eq (Imported.nat_S x) (Imported.nat_S y).
Proof.
  intros x y H. destruct H. apply IsomorphismDefinitions.eq_refl.
Qed.

Lemma S_cong : forall x y : Datatypes.nat, 
  IsomorphismDefinitions.eq x y -> 
  IsomorphismDefinitions.eq (Datatypes.S x) (Datatypes.S y).
Proof.
  intros x y H. destruct H. apply IsomorphismDefinitions.eq_refl.
Qed.

Lemma nat_to_from : forall x : Imported.nat, 
  IsomorphismDefinitions.eq (nat_to_imported (imported_to_nat x)) x.
Proof.
  intro x. induction x.
  - simpl. apply IsomorphismDefinitions.eq_refl.
  - simpl. apply natS_cong. exact IHx.
Qed.

Lemma nat_from_to : forall x : Datatypes.nat, 
  IsomorphismDefinitions.eq (imported_to_nat (nat_to_imported x)) x.
Proof.
  intro x. induction x.
  - simpl. apply IsomorphismDefinitions.eq_refl.
  - simpl. apply S_cong. exact IHx.
Qed.

Instance nat_iso : Iso Datatypes.nat imported_nat :=
  @Build_Iso Datatypes.nat Imported.nat nat_to_imported imported_to_nat nat_to_from nat_from_to.

Instance: KnownConstant Datatypes.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.nat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Datatypes.nat nat_iso := {}.
Instance: IsoStatementProofBetween Datatypes.nat Imported.nat nat_iso := {}.