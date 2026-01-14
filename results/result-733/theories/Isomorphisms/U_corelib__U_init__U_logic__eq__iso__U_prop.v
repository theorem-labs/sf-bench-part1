From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* For Prop: we need an equality type in SProp for SProp arguments *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp :=
  @Imported.Corelib_Init_Logic_eq_Prop.

(* Helper to get from SProp back - using that SProp is proof-irrelevant *)
Lemma sprop_iso_injective : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (a b : x1),
  a = b.
Proof.
  intros x1 x2 hx a b.
  pose proof (from_to hx a) as Ha.
  pose proof (from_to hx b) as Hb.
  pose proof (eq_of_seq Ha) as Ha'.
  pose proof (eq_of_seq Hb) as Hb'.
  rewrite <- Ha', <- Hb'.
  reflexivity.
Qed.

Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) 
  (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> 
  forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> 
  Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  unfold imported_Corelib_Init_Logic_eq_Prop.
  unshelve eapply Build_Iso.
  - intro Heq. 
    destruct H34, H56, Heq.
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
  - intro Hs. 
    apply (sprop_iso_injective hx).
  - intro s. reflexivity.
  - intro Heq.
    apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) imported_Corelib_Init_Logic_eq_Prop Corelib_Init_Logic_eq_iso_Prop := {}.
