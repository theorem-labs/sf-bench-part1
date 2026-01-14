From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso. (* for speed *)

From IsomorphismChecker Require Export Isomorphisms.le__iso.

Definition imported_ge : imported_nat -> imported_nat -> SProp := Imported.ge.

(* ge m n = le n m in Rocq, and Imported.ge m n = Imported.le n m *)

(* Convert Rocq ge to Imported.ge *)
Definition ge_to_imported (m n : Datatypes.nat) (H : Peano.ge m n) : Imported.ge (nat_to_imported m) (nat_to_imported n).
Proof.
  unfold Peano.ge in H. unfold Imported.ge.
  (* H : le n m, goal: Imported.le (nat_to_imported n) (nat_to_imported m) *)
  exact (@le_to_imported n m H).
Defined.

(* Convert Imported.ge to Rocq ge *)
Definition imported_to_ge (m' n' : Imported.nat) (H : Imported.ge m' n') : Peano.ge (nat_from_imported m') (nat_from_imported n').
Proof.
  unfold Imported.ge in H. unfold Peano.ge.
  (* H : Imported.le n' m', goal: le (nat_from_imported n') (nat_from_imported m') *)
  exact (@imported_to_le n' m' H).
Defined.

Instance ge_iso : forall (x1 : Datatypes.nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> forall (x3 : Datatypes.nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> Iso (Peano.ge x1 x3) (imported_ge x2 x4).
Proof.
  intros x1 x2 H12 x3 x4 H34.
  unfold rel_iso in H12, H34. simpl in H12, H34.
  unfold imported_ge.
  
  apply IsoEq.eq_of_seq in H12.
  apply IsoEq.eq_of_seq in H34.
  subst x2 x4.
  
  apply iso_Prop_to_SProp.
  { exact (@ge_to_imported x1 x3). }
  { intro H.
    pose (@imported_to_ge (nat_to_imported x1) (nat_to_imported x3) H) as H'.
    rewrite nat_from_to in H'.
    rewrite nat_from_to in H'.
    exact H'. }
Defined.

Instance: KnownConstant Peano.ge := {}.
Instance: KnownConstant Imported.ge := {}.
Instance: IsoStatementProofFor Peano.ge ge_iso := {}.
Instance: IsoStatementProofBetween Peano.ge Imported.ge ge_iso := {}.