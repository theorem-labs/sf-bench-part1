From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.

Local Open Scope nat_scope.

From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_le : imported_nat -> imported_nat -> SProp := Imported.le.

(* Helper functions to convert between Datatypes.nat and Imported.nat *)
Definition nat_to_imported : Datatypes.nat -> imported_nat := to nat_iso.
Definition nat_from_imported : imported_nat -> Datatypes.nat := from nat_iso.

Lemma nat_to_from : forall n, nat_to_imported (nat_from_imported n) = n.
Proof.
  intro n. unfold nat_to_imported, nat_from_imported.
  apply IsoEq.eq_of_seq. apply to_from.
Qed.

Lemma nat_from_to : forall n, nat_from_imported (nat_to_imported n) = n.
Proof.
  intro n. unfold nat_to_imported, nat_from_imported.
  apply IsoEq.eq_of_seq. apply from_to.
Qed.

(* le_to_imported: convert Rocq le to Imported.le (inductive) *)
Definition le_to_imported : forall (n m : Datatypes.nat), Peano.le n m -> Imported.le (nat_to_imported n) (nat_to_imported m).
Proof.
  fix IH 3.
  intros n m H.
  destruct H.
  { apply Imported.le_le_n. }
  { simpl. apply Imported.le_le_S. apply IH. exact H. }
Defined.

(* imported_to_le: convert Imported.le (inductive in SProp) to Rocq le *)
(* Use le_sind eliminator into SProp, then sinhabitant to extract *)

Definition imported_le_to_sinhabited_le : forall (n' m' : imported_nat), Imported.le n' m' ->
  SInhabited (Peano.le (nat_from_imported n') (nat_from_imported m')).
Proof.
  intros n' m' H.
  exact (@Imported.le_sind n' 
    (fun m'' _ => SInhabited (Peano.le (nat_from_imported n') (nat_from_imported m'')))
    (sinhabits (Peano.le_n _))
    (fun m'' _ IH => sinhabits (Peano.le_S _ _ (sinhabitant IH)))
    m' H).
Defined.

Definition imported_to_le : forall (n' m' : imported_nat), Imported.le n' m' -> 
  Peano.le (nat_from_imported n') (nat_from_imported m').
Proof.
  intros n' m' H.
  exact (sinhabitant (@imported_le_to_sinhabited_le n' m' H)).
Defined.

(* Build an iso between Prop P and SProp S when they're equivalent *)
Definition iso_Prop_to_SProp (P : Prop) (S : SProp) (to : P -> S) (from : S -> P) : Iso P S :=
  @Build_Iso P S to from 
    (fun x => IsomorphismDefinitions.eq_refl) 
    (fun x => seq_of_eq (Stdlib.Logic.ProofIrrelevance.proof_irrelevance P (from (to x)) x)).

(* The isomorphism *)
Instance le_iso : (forall (x1 : Datatypes.nat) (x2 : imported_nat) (_ : @rel_iso Datatypes.nat imported_nat nat_iso x1 x2) (x3 : Datatypes.nat) (x4 : imported_nat) (_ : @rel_iso Datatypes.nat imported_nat nat_iso x3 x4), Iso (Peano.le x1 x3) (imported_le x2 x4)).
Proof.
  intros x1 x2 H12 x3 x4 H34.
  unfold rel_iso in H12, H34. simpl in H12, H34.
  unfold imported_le.
  
  apply IsoEq.eq_of_seq in H12.
  apply IsoEq.eq_of_seq in H34.
  subst x2 x4.
  
  apply iso_Prop_to_SProp.
  { exact (@le_to_imported x1 x3). }
  { intro H.
    pose (@imported_to_le (nat_to_imported x1) (nat_to_imported x3) H) as H'.
    rewrite nat_from_to in H'.
    rewrite nat_from_to in H'.
    exact H'. }
Defined.

Instance: KnownConstant Peano.le := {}. 
Instance: KnownConstant Imported.le := {}. 
Instance: IsoStatementProofFor Peano.le le_iso := {}.
Instance: IsoStatementProofBetween Peano.le Imported.le le_iso := {}.
