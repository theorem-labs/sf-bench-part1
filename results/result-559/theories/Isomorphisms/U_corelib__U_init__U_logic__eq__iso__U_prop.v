From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Imported.Corelib_Init_Logic_eq_Prop is now in SProp *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For Prop types mapped to SProp, we build an explicit isomorphism *)
(* Using the recl eliminator to construct the from function *)
Definition eq_iso_Prop_from (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x5 : x1)
  : imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) -> x3 = x5.
Proof.
  intro Hseq.
  pose proof (Imported.Corelib_Init_Logic_eq_Prop_recl x2 (to hx x3) (fun y _ => from hx (to hx x3) = from hx y) Logic.eq_refl (to hx x5) Hseq) as H.
  rewrite (from_to hx x3) in H.
  rewrite (from_to hx x5) in H.
  exact H.
Defined.

Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  unshelve eapply Build_Iso.
  - intro Heq.
    destruct H34. destruct H56. destruct Heq.
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
  - intro Hseq.
    destruct H34. destruct H56.
    exact (eq_iso_Prop_from hx x3 x5 Hseq).
  - intro Hseq.
    apply IsomorphismDefinitions.eq_refl.
  - intro Heq.
    destruct H34. destruct H56. destruct Heq.
    apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
