From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso. (* for speed *)

Local Open Scope nat_scope.

From IsomorphismChecker Require Export Isomorphisms.le__iso.

Definition imported_lt : imported_nat -> imported_nat -> SProp := Imported.lt.

(* lt n m = le (S n) m in Rocq, and Imported.lt n m = Imported.le (Imported.nat_S n) m *)

(* Convert Rocq lt to Imported.lt *)
Definition lt_to_imported (n m : Datatypes.nat) (H : Peano.lt n m) : Imported.lt (nat_to_imported n) (nat_to_imported m).
Proof.
  unfold Peano.lt in H. unfold Imported.lt.
  (* H : le (S n) m, goal: Imported.le (Imported.nat_S (nat_to_imported n)) (nat_to_imported m) *)
  simpl.
  exact (@le_to_imported (S n) m H).
Defined.

(* Convert Imported.lt to Rocq lt *)
Definition imported_to_lt (n' m' : Imported.nat) (H : Imported.lt n' m') : Peano.lt (nat_from_imported n') (nat_from_imported m').
Proof.
  unfold Imported.lt in H. unfold Peano.lt.
  (* H : Imported.le (Imported.nat_S n') m', goal: le (S (nat_from_imported n')) (nat_from_imported m') *)
  pose proof (@imported_to_le (Imported.nat_S n') m' H) as H'.
  simpl in H'.
  exact H'.
Defined.

Instance lt_iso : (forall (x1 : nat) (x2 : imported_nat) (_ : @rel_iso nat imported_nat nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (_ : @rel_iso nat imported_nat nat_iso x3 x4), Iso (lt x1 x3) (imported_lt x2 x4)).
Proof.
  intros x1 x2 H12 x3 x4 H34.
  unfold rel_iso in H12, H34. simpl in H12, H34.
  unfold imported_lt.
  
  apply IsoEq.eq_of_seq in H12.
  apply IsoEq.eq_of_seq in H34.
  subst x2 x4.
  
  apply iso_Prop_to_SProp.
  { exact (@lt_to_imported x1 x3). }
  { intro H.
    pose (@imported_to_lt (nat_to_imported x1) (nat_to_imported x3) H) as H'.
    rewrite nat_from_to in H'.
    rewrite nat_from_to in H'.
    exact H'. }
Defined.

Instance: KnownConstant lt := {}.
Instance: KnownConstant Imported.lt := {}.
Instance: IsoStatementProofFor lt lt_iso := {}.
Instance: IsoStatementProofBetween lt Imported.lt lt_iso := {}.