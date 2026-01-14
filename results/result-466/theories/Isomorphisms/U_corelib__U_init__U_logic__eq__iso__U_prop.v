From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* For Prop arguments, we use the imported SProp equality *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := 
  @Imported.Corelib_Init_Logic_eq_Prop.

Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in *.
  unfold imported_Corelib_Init_Logic_eq_Prop.
  unshelve eapply Build_Iso.
  - (* to: eq in Prop -> Imported.Corelib_Init_Logic_eq_Prop x4 x6 *)
    intro Heq.
    destruct Heq.
    (* We have H34: hx x3 = x4 and H56: hx x3 = x6, and we need to prove x4 = x6 *)
    (* Use IsoEq.eq_srect to transport refl along SProp equality *)
    pose proof (IsoEq.eq_trans (IsoEq.eq_sym H34) H56) as Heq46.
    exact (IsoEq.eq_srect (fun y => Imported.Corelib_Init_Logic_eq_Prop x2 x4 y)
             (Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4) Heq46).
  - (* from: Imported.Corelib_Init_Logic_eq_Prop x4 x6 -> eq x3 x5 *)
    intro Heq.
    pose (Hfrom34 := from_to hx x3). 
    pose (Hfrom56 := from_to hx x5).
    (* Use the eliminator for Imported.Corelib_Init_Logic_eq_Prop *)
    pose proof (Imported.Corelib_Init_Logic_eq_Prop_indl x2 x4 
            (fun y _ => IsomorphismDefinitions.eq (from hx x4) (from hx y))
            IsomorphismDefinitions.eq_refl x6 Heq) as Hfrom46.
    pose (step1 := IsoEq.f_equal (from hx) H34). 
    pose (step2 := IsoEq.eq_trans step1 Hfrom46).
    pose (step3 := IsoEq.f_equal (from hx) (IsoEq.eq_sym H56)). 
    pose (step4 := IsoEq.eq_trans step2 step3). 
    pose (step5 := IsoEq.eq_trans (IsoEq.eq_sym Hfrom34) step4). 
    pose (step6 := IsoEq.eq_trans step5 Hfrom56). 
    exact (IsoEq.eq_of_seq step6).
  - (* to_from *)
    intro Heq.
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro Heq.
    destruct Heq.
    apply sUIPt.
Defined.

Instance: KnownConstant imported_Corelib_Init_Logic_eq_Prop := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) imported_Corelib_Init_Logic_eq_Prop Corelib_Init_Logic_eq_iso_Prop := {}.
