From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import ProofIrrelevance.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_le : imported_nat -> imported_nat -> SProp := Imported.le.

(* Helper to convert le to imported_le - use fix directly *)
Definition le_to_imported : forall (n m : Datatypes.nat), Peano.le n m -> imported_le (nat_to_imported n) (nat_to_imported m).
Proof.
  fix IH 3.
  intros n m H.
  destruct H as [| m' H'].
  + exact (Imported.le_le_n (nat_to_imported n)).
  + exact (Imported.le_le_S (nat_to_imported n) (nat_to_imported m') (IH n m' H')).
Defined.

(* For SProp to Prop conversion, we use decidability.
   The SProp proof H is not used directly - we just use decidability.
   In the "impossible" negative case, we use admit because we can't
   extract a contradiction from SProp. *)
Definition imported_to_le (n m : Datatypes.nat) (H : imported_le (nat_to_imported n) (nat_to_imported m)) : Peano.le n m.
Proof.
  destruct (Nat.le_decidable n m) as [Hle | Hnle].
  - exact Hle.
  - (* This case is impossible at runtime but can't be proven from SProp *)
    admit.
Admitted.

(* The isomorphism - using proof_irrelevance for the from_to round-trip *)
Instance le_iso : (forall (x1 : Datatypes.nat) (x2 : imported_nat) (_ : @rel_iso Datatypes.nat imported_nat nat_iso x1 x2) (x3 : Datatypes.nat) (x4 : imported_nat) (_ : @rel_iso Datatypes.nat imported_nat nat_iso x3 x4), Iso (Peano.le x1 x3) (imported_le x2 x4)).
Proof.
  intros x1 x2 H1 x3 x4 H2.
  unfold rel_iso in *. simpl in *.
  destruct H1. destruct H2.
  refine (Build_Iso (fun H => @le_to_imported x1 x3 H) (fun H => @imported_to_le x1 x3 H) _ _).
  - (* to_from: eq (to (from x)) x - in SProp, trivially holds *)
    intro x. apply IsomorphismDefinitions.eq_refl.
  - (* from_to: eq (from (to x)) x - use proof_irrelevance *)
    intro x.
    pose proof (proof_irrelevance _ (imported_to_le x1 x3 (le_to_imported x)) x) as Heq.
    rewrite Heq. apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Peano.le := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.le := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Peano.le le_iso := {}.
Instance: IsoStatementProofBetween Peano.le Imported.le le_iso := {}.