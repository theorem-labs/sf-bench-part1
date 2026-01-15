From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.

From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Local Open Scope nat_scope.

Definition imported_le : imported_nat -> imported_nat -> SProp := Imported.le.

(* Helper: convert nat to imported nat and back *)
Lemma nat_to_from : forall x : nat, imported_to_nat (nat_to_imported x) = x.
Proof.
  induction x; simpl; [reflexivity | f_equal; assumption].
Defined.

(* Forward: Peano.le -> Imported.nat_le (SProp) - this direction is easy *)
Definition le_to_nat_le : forall (n m : nat), Peano.le n m -> Imported.nat_le (nat_to_imported n) (nat_to_imported m).
Proof.
  intros n m H.
  induction H as [|m' H' IH].
  - exact (Imported.nat_le_le_n _).
  - exact (Imported.nat_le_le_S _ _ IH).
Defined.

(* Backward: Imported.nat_le (SProp) -> SInhabited (Peano.le) - use eliminator to target SProp *)
Definition nat_le_to_le_sinhabited : forall (n m : Imported.nat), Imported.nat_le n m -> SInhabited (Peano.le (imported_to_nat n) (imported_to_nat m)).
Proof.
  intros n m H.
  refine (Imported.nat_le_sind n 
    (fun m' _ => SInhabited (Peano.le (imported_to_nat n) (imported_to_nat m')))
    _ _ m H).
  - exact (sinhabits (le_n _)).
  - intros m' _ IH.
    destruct IH as [IH_proof].
    simpl.
    exact (sinhabits (le_S _ _ IH_proof)).
Defined.

(* The isomorphism *)
Instance le_iso : (forall (x1 : nat) (x2 : imported_nat) (_ : @rel_iso nat imported_nat nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (_ : @rel_iso nat imported_nat nat_iso x3 x4), Iso (Peano.le x1 x3) (imported_le x2 x4)).
Proof.
  intros x1 x2 H12 x3 x4 H34.
  destruct H12 as [H12]. destruct H34 as [H34].
  simpl in H12, H34.
  unfold imported_le, Imported.le.
  
  apply IsoEq.eq_of_seq in H12.
  apply IsoEq.eq_of_seq in H34.
  subst x2 x4.
  
  unshelve refine {|
    to := fun (H : Peano.le x1 x3) => @le_to_nat_le x1 x3 H;
    from := fun H => _ 
  |}.
  - (* from: Imported.nat_le -> Peano.le *)
    pose (@nat_le_to_le_sinhabited (nat_to_imported x1) (nat_to_imported x3) H) as Hsi.
    apply sinhabitant in Hsi.
    rewrite !nat_to_from in Hsi.
    exact Hsi.
  - intro. apply IsomorphismDefinitions.eq_refl.
  - intro x. apply IsoEq.seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant le := {}. 
Instance: KnownConstant Imported.le := {}. 
Instance: IsoStatementProofFor le le_iso := {}.
Instance: IsoStatementProofBetween le Imported.le le_iso := {}.
