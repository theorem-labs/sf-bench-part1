From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.
(* Don't require the main eq__iso file - let the main file require us instead *)

(* Imported.Corelib_Init_Logic_eq_Prop is for SProp arguments *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For Prop equality with an iso from Type to SProp *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  unfold imported_Corelib_Init_Logic_eq_Prop.
  unshelve eapply Build_Iso.
  + (* to *)
    intro Heq.
    destruct H34. destruct H56. destruct Heq.
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
  + (* from *)
    intro Hseq.
    destruct H34. destruct H56.
    (* Now Hseq : Imported.Corelib_Init_Logic_eq_Prop x2 (hx x3) (hx x5) *)
    (* We need to show x3 = x5 : x1 *)
    (* Use the recl principle which can produce Type result *)
    pose proof (from_to hx x3) as Hx3.
    pose proof (from_to hx x5) as Hx5.
    (* Use the eliminator to get from (hx x3) = from (hx x5) *)
    assert (H: from hx (hx x3) = from hx (hx x5)).
    {
      exact (Imported.Corelib_Init_Logic_eq_Prop_recl x2 (hx x3) (fun y _ => from hx (hx x3) = from hx y) Logic.eq_refl (hx x5) Hseq).
    }
    rewrite Hx3 in H. rewrite Hx5 in H. exact H.
  + (* to_from *)
    intro Hseq. reflexivity.
  + (* from_to *)
    intro Heq.
    destruct H34. destruct H56. destruct Heq.
    simpl.
    (* Use proof irrelevance *)
    apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
