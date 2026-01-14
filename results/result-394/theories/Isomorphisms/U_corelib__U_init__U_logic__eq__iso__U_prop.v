From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := (@Imported.Corelib_Init_Logic_eq_Prop).

Definition eq_from_imported_eq_Prop {A : Type} {B : SProp} (i : Iso A B) {x y : A} 
  (H : Imported.Corelib_Init_Logic_eq_inst1 B (to i x) (to i y)) : x = y.
Proof.
  assert (from i (to i x) = from i (to i y)) as Hf.
  { destruct H. reflexivity. }
  rewrite (eq_of_seq (from_to i x)) in Hf.
  rewrite (eq_of_seq (from_to i y)) in Hf.
  exact Hf.
Defined.

Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 h34 x5 x6 h56.
  unfold imported_Corelib_Init_Logic_eq_Prop.
  unfold Imported.Corelib_Init_Logic_eq_Prop.
  unfold rel_iso in *.
  destruct h34, h56.
  unshelve eapply Build_Iso.
  - intro H. destruct H. apply Imported.Corelib_Init_Logic_eq_refl_inst1.
  - exact (eq_from_imported_eq_Prop hx).
  - intro x. apply IsomorphismDefinitions.eq_refl.
  - intro x. apply seq_of_eq. apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
