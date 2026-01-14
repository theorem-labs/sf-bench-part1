From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For Prop equality, both sides are proof-irrelevant *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in *.
  unfold imported_Corelib_Init_Logic_eq_Prop.
  unshelve eapply Build_Iso.
  - (* to: eq in Prop -> imported eq in SProp *)
    intro Heq.
    destruct Heq.
    (* We have H34: hx x3 = x4 and H56: hx x3 = x6 *)
    (* Use the eliminator *)
    exact (IsoEq.eq_srect (fun y => Imported.Corelib_Init_Logic_eq_Prop x2 y x6)
             (IsoEq.eq_srect (fun z => Imported.Corelib_Init_Logic_eq_Prop x2 x4 z)
                (Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4)
                (IsoEq.eq_trans (IsoEq.eq_sym H34) H56))
             IsomorphismDefinitions.eq_refl).
  - (* from: imported eq in SProp -> eq in Prop *)
    intro Heq.
    pose (Hfrom34 := from_to hx x3).
    pose (Hfrom56 := from_to hx x5).
    pose (from_x4_eq_from_x6 := Imported.Corelib_Init_Logic_eq_Prop_indl x2 x4 
            (fun y _ => IsomorphismDefinitions.eq (from hx x4) (from hx y))
            IsomorphismDefinitions.eq_refl x6 Heq).
    pose (step1 := IsoEq.f_equal (from hx) H34).
    pose (step2 := IsoEq.eq_trans step1 from_x4_eq_from_x6).
    pose (step3 := IsoEq.f_equal (from hx) (IsoEq.eq_sym H56)).
    pose (step4 := IsoEq.eq_trans step2 step3).
    pose (step5 := IsoEq.eq_trans (IsoEq.eq_sym Hfrom34) step4).
    pose (step6 := IsoEq.eq_trans step5 Hfrom56).
    exact (IsoEq.eq_of_seq step6).
  - (* to_from: both are SProp, they're definitionally equal *)
    intro Heq.
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to: use UIP for Prop equality *)
    intro Heq.
    destruct Heq.
    apply sUIPt.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
