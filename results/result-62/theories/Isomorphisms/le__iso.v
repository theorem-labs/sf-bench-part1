From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.

From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_le : imported_nat -> imported_nat -> SProp := Imported.le.

(* Convert Peano.le to Imported.le *)
Definition le_to_imported (n m : nat) (H : Peano.le n m) : Imported.le (nat_to_imported n) (nat_to_imported m).
Proof.
  induction H.
  - apply Imported.le_le_n.
  - apply Imported.le_le_S. exact IHle.
Defined.

(* Convert Imported.le to Peano.le - we need to use the recursor *)
(* Since le lives in SProp, we can only get SInhabited Prop *)
Definition imported_to_le_sinhabited : forall (n' m' : Imported.nat), Imported.le n' m' -> SInhabited (Peano.le (nat_from_imported n') (nat_from_imported m')).
Proof.
  intros n' m' H.
  revert m' H.
  apply (Imported.le_indl n' (fun m'' _ => SInhabited (Peano.le (nat_from_imported n') (nat_from_imported m'')))).
  - apply sinhabits. apply Peano.le_n.
  - intros m'' _ IH. 
    apply sinhabits.
    apply Peano.le_S.
    exact (sinhabitant IH).
Defined.

Definition imported_to_le (n' m' : Imported.nat) (H : Imported.le n' m') : Peano.le (nat_from_imported n') (nat_from_imported m') :=
  sinhabitant (@imported_to_le_sinhabited n' m' H).

Lemma nat_roundtrip : forall n, nat_from_imported (nat_to_imported n) = n.
Proof.
  fix IH 1.
  intros n. destruct n.
  - reflexivity.
  - simpl. f_equal. apply IH.
Defined.

#[local] Unset Universe Polymorphism.
Instance le_iso : forall (x1 : nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> forall (x3 : nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> Iso (Peano.le x1 x3) (imported_le x2 x4).
Proof.
  intros x1 x2 H12 x3 x4 H34.
  unfold imported_le.
  pose proof (eq_of_seq (proj_rel_iso H12)) as E12.
  pose proof (eq_of_seq (proj_rel_iso H34)) as E34.
  subst x2 x4.
  unshelve refine {|
    to := @le_to_imported x1 x3;
    from := fun H => _
  |}.
  - pose (@imported_to_le (nat_to_imported x1) (nat_to_imported x3) H) as H'.
    rewrite nat_roundtrip in H'.
    rewrite nat_roundtrip in H'.
    exact H'.
  - intro. apply IsomorphismDefinitions.eq_refl.
  - intro x. apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant le := {}.
Instance: KnownConstant Imported.le := {}.
Instance: IsoStatementProofFor le le_iso := {}.
Instance: IsoStatementProofBetween le Imported.le le_iso := {}.
