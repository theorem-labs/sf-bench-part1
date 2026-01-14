From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso. (* for speed *)

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := (@Imported.Corelib_Init_Logic_eq_Prop).

Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), 
  rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 h34 x5 x6 h56.
  unfold imported_Corelib_Init_Logic_eq_Prop.
  unfold Imported.Corelib_Init_Logic_eq_Prop.
  unfold rel_iso in *.
  destruct h34, h56.
  unshelve eapply Build_Iso.
  - (* to : x3 = x5 -> Imported.Corelib_Init_Logic_eq_inst1 x2 (to hx x3) (to hx x5) *)
    intro H. destruct H. exact (Imported.Corelib_Init_Logic_eq_refl_inst1 x2 (to hx x3)).
  - (* from : Imported.Corelib_Init_Logic_eq_inst1 x2 (to hx x3) (to hx x5) -> x3 = x5 *)
    intro H. 
    assert (from hx (to hx x3) = from hx (to hx x5)) as Hf.
    { destruct H. reflexivity. }
    rewrite (eq_of_seq (from_to hx x3)) in Hf.
    rewrite (eq_of_seq (from_to hx x5)) in Hf.
    exact Hf.
  - (* to_from *) intro x. apply IsomorphismDefinitions.eq_refl.
  - (* from_to *) intro x. apply seq_of_eq. apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
