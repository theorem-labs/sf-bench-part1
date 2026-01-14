From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_Nat_pred : imported_nat -> imported_nat := Imported.Nat_pred.

(* Prove that pred commutes with the isomorphism *)
Lemma pred_commutes : forall n : nat,
  Logic.eq (nat_to_imported (Nat.pred n)) (Imported.Nat_pred (nat_to_imported n)).
Proof.
  intros n. destruct n as [| n']; simpl.
  - reflexivity.
  - reflexivity.
Qed.

Instance Nat_pred_iso : forall (x1 : nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> rel_iso nat_iso (Nat.pred x1) (imported_Nat_pred x2).
Proof.
  intros x1 x2 H.
  unfold rel_iso in *. simpl in *.
  unfold imported_Nat_pred.
  (* H : nat_to_imported x1 = x2 (in SProp) *)
  pose proof (eq_of_seq H) as E.
  apply seq_of_eq.
  transitivity (Imported.Nat_pred (nat_to_imported x1)).
  - apply pred_commutes.
  - apply Logic.f_equal. exact E.
Defined.
Instance: KnownConstant Nat.pred := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Nat_pred := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Nat.pred Nat_pred_iso := {}.
Instance: IsoStatementProofBetween Nat.pred Imported.Nat_pred Nat_pred_iso := {}.