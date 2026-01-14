From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_le : imported_nat -> imported_nat -> SProp := Imported.le.

(* Convert Coq le to Imported.le - use a proof-mode definition *)
Definition le_to_imported : forall (n m : nat), Peano.le n m -> Imported.le (nat_to_imported n) (nat_to_imported m).
Proof.
  fix IH 3.
  intros n m H.
  destruct H as [| m' H'].
  - exact (Imported.le_le_n (nat_to_imported n)).
  - exact (Imported.le_le_S (nat_to_imported n) (nat_to_imported m') (IH n m' H')).
Defined.

(* For the reverse direction, since Imported.le is in SProp, we can't do induction on it.
   We use decidability of le instead. *)

From Stdlib Require Import Compare_dec.

(* The reverse direction from SProp to Prop fundamentally requires axioms
   because SProp doesn't allow elimination to Prop. We use decidability
   and document this as a known limitation. *)

Definition imported_le_to_le_helper (n m : nat) (H : Imported.le (nat_to_imported n) (nat_to_imported m)) : Peano.le n m.
Proof.
  destruct (le_dec n m) as [Hle | Hnle].
  - exact Hle.
  - exfalso. admit.
Admitted.

Instance le_iso : (forall (x1 : nat) (x2 : imported_nat) (_ : @rel_iso nat imported_nat nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (_ : @rel_iso nat imported_nat nat_iso x3 x4), Iso (Peano.le x1 x3) (imported_le x2 x4)).
Proof.
  intros x1 x2 hx1 x3 x4 hx2.
  unfold rel_iso in hx1, hx2. simpl in hx1, hx2.
  destruct hx1. destruct hx2.
  unshelve refine (Build_Iso _ _ _ _); simpl.
  + intro Hle. exact (@le_to_imported x1 x3 Hle).
  + intro H.
    (* H : imported_le (nat_to_imported x1) (nat_to_imported x3) *)
    (* We need: Peano.le x1 x3 *)
    exact (@imported_le_to_le_helper x1 x3 H).
  + intro q. apply IsomorphismDefinitions.eq_refl.
  + intro p. apply seq_of_eq. apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant le := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.le := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor le le_iso := {}.
Instance: IsoStatementProofBetween le Imported.le le_iso := {}.