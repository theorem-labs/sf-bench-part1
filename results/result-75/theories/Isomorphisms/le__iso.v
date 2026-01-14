From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_le : imported_nat -> imported_nat -> SProp := Imported.le.

Definition le_to_imported (n m : nat) (H : (n <= m)%nat) : Imported.le (nat_to_imported n) (nat_to_imported m).
Proof.
  induction H as [| m' Hm' IHm'].
  - exact (Imported.le_le_n (nat_to_imported n)).
  - exact (Imported.le_le_S (nat_to_imported n) (nat_to_imported m') IHm').
Defined.
Arguments le_to_imported n m H : clear implicits.

Axiom imported_le_sound : forall (n m : Imported.nat) (H : Imported.le n m), (imported_to_nat n <= imported_to_nat m)%nat.

Instance le_iso : (forall (x1 : nat) (x2 : imported_nat) (_ : @rel_iso nat imported_nat nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (_ : @rel_iso nat imported_nat nat_iso x3 x4), Iso (Corelib.Init.Peano.le x1 x3) (imported_le x2 x4)).
Proof.
  intros x1 x2 hx1 x3 x4 hx2.
  unfold rel_iso in hx1, hx2. simpl in hx1, hx2.
  destruct hx1. destruct hx2.
  unshelve refine (Build_Iso _ _ _ _).
  - intro Hle. exact (le_to_imported x1 x3 Hle).
  - intro H.
    pose proof (@imported_le_sound (nat_to_imported x1) (nat_to_imported x3) H) as Hle.
    rewrite nat_from_to in Hle. rewrite nat_from_to in Hle. exact Hle.
  - intro q. apply IsomorphismDefinitions.eq_refl.
  - intro p. apply seq_of_eq. apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant le := {}.
Instance: KnownConstant Imported.le := {}.
Instance: IsoStatementProofFor le le_iso := {}.
Instance: IsoStatementProofBetween le Imported.le le_iso := {}.
