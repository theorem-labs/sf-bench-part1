From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
From Stdlib Require Import Logic.ProofIrrelevance.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := 
  @Imported.Corelib_Init_Logic_eq_Prop.

Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unshelve eapply Build_Iso.
  - intro Heq. destruct Heq. unfold imported_Corelib_Init_Logic_eq_Prop.
    pose proof (eq_trans (eq_sym H34) H56) as H46.
    destruct H46. exact (Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4).
  - intro Heq. unfold imported_Corelib_Init_Logic_eq_Prop in Heq.
    pose proof (from_to hx x3) as FT3. pose proof (from_to hx x5) as FT5.
    pose proof (@IsomorphismDefinitions.eq_rect x2 (to hx x3) (fun y _ => from hx y = x3) 
      (eq_of_seq FT3) x4 H34) as HX3.
    pose proof (@IsomorphismDefinitions.eq_rect x2 (to hx x5) (fun y _ => from hx y = x5) 
      (eq_of_seq FT5) x6 H56) as HX5.
    exact (Corelib.Init.Logic.eq_trans (Corelib.Init.Logic.eq_sym HX3) HX5).
  - intro Heq. apply IsomorphismDefinitions.eq_refl.
  - intro Heq. apply seq_of_eq. apply proof_irrelevance.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
