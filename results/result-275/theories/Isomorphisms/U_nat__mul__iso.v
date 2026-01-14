From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_Nat_mul : imported_nat -> imported_nat -> imported_nat := Imported.Nat_mul.

(* Prove properties of imported operations by induction *)
Lemma imported_add_correct : forall a b : imported_nat,
  imported_to_nat (Imported.Nat_add a b) = (imported_to_nat a + imported_to_nat b)%nat.
Proof.
  intros a. induction a using Imported.nat_rec; intro b.
  - reflexivity.
  - change (imported_to_nat (Imported.Nat_add (Imported.nat_succ a) b) = 
            S (imported_to_nat a + imported_to_nat b)).
    (* Both sides should compute to the same thing *)
    transitivity (S (imported_to_nat (Imported.Nat_add a b))).
    + reflexivity.
    + f_equal. apply IHa.
Qed.

Lemma imported_mul_correct : forall a b : imported_nat,
  imported_to_nat (Imported.Nat_mul a b) = (imported_to_nat a * imported_to_nat b)%nat.
Proof.
  intros a. induction a using Imported.nat_rec; intro b.
  - reflexivity.
  - change (imported_to_nat (Imported.Nat_mul (Imported.nat_succ a) b) = 
            (imported_to_nat b + imported_to_nat a * imported_to_nat b)%nat).
    transitivity (imported_to_nat (Imported.Nat_add (Imported.Nat_mul a b) b)).
    + reflexivity.
    + transitivity (imported_to_nat (Imported.Nat_mul a b) + imported_to_nat b)%nat.
      * apply imported_add_correct.
      * pose proof (IHa b) as H.
        transitivity (imported_to_nat a * imported_to_nat b + imported_to_nat b)%nat.
        -- f_equal. exact H.
        -- apply PeanoNat.Nat.add_comm.
Qed.

Lemma nat_mul_iso_aux : forall n m : nat,
  IsomorphismDefinitions.eq (nat_to_imported (n * m)) (Imported.Nat_mul (nat_to_imported n) (nat_to_imported m)).
Proof.
  intros n m.
  apply (@eq_trans imported_nat _ (nat_to_imported (imported_to_nat (Imported.Nat_mul (nat_to_imported n) (nat_to_imported m)))) _).
  - apply IsoEq.f_equal.
    apply seq_of_eq.
    pose proof (imported_mul_correct (nat_to_imported n) (nat_to_imported m)) as H.
    rewrite !from_to_nat in H.
    symmetry. exact H.
  - apply to_from_nat.
Qed.

Instance Nat_mul_iso : forall (x1 : nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> forall (x3 : nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> rel_iso nat_iso (x1 * x3) (imported_Nat_mul x2 x4).
Proof.
  intros x1 x2 h1 x3 x4 h3.
  unfold rel_iso, nat_iso in *. simpl in *.
  unfold imported_Nat_mul.
  apply (@eq_trans imported_nat _ (Imported.Nat_mul (nat_to_imported x1) (nat_to_imported x3)) _).
  - apply nat_mul_iso_aux.
  - apply f_equal2; assumption.
Qed.

Instance: KnownConstant Nat.mul := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Nat_mul := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Nat.mul Nat_mul_iso := {}.
Instance: IsoStatementProofBetween Nat.mul Imported.Nat_mul Nat_mul_iso := {}.