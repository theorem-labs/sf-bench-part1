From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

(* Standalone - no dependency on main eq iso file *)

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For Prop-typed equality, both sides are in SProp *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2),
  rel_iso hx x3 x4 ->
  forall (x5 : x1) (x6 : x2),
  rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in *.
  unfold imported_Corelib_Init_Logic_eq_Prop.
  unshelve eapply Build_Iso.
  - (* to: eq in Prop -> imported eq in SProp *)
    intro Heq.
    destruct Heq.
    (* H34: hx x3 = x4, H56: hx x3 = x6, need x4 = x6 *)
    exact (IsoEq.eq_srect (fun y => Imported.Corelib_Init_Logic_eq_Prop x2 y x6)
             (IsoEq.eq_srect (fun z => Imported.Corelib_Init_Logic_eq_Prop x2 (to hx x3) z)
                (Imported.Corelib_Init_Logic_eq_Prop_refl x2 (to hx x3))
                H56)
             H34).
  - (* from: imported eq in SProp -> eq in Prop *)
    intro Heq.
    pose (from_x4_eq_from_x6 := Imported.Corelib_Init_Logic_eq_Prop_indl x2 x4
            (fun y _ => IsomorphismDefinitions.eq (from hx x4) (from hx y))
            IsomorphismDefinitions.eq_refl x6 Heq).
    pose (step1 := IsoEq.f_equal (from hx) H34).
    pose (step2 := IsoEq.eq_trans step1 from_x4_eq_from_x6).
    pose (step3 := IsoEq.f_equal (from hx) (IsoEq.eq_sym H56)).
    pose (step4 := IsoEq.eq_trans step2 step3).
    pose (step5 := IsoEq.eq_trans (IsoEq.eq_sym (from_to hx x3)) step4).
    pose (step6 := IsoEq.eq_trans step5 (from_to hx x5)).
    exact (IsoEq.eq_of_seq step6).
  - (* to_from *)
    intro Heq.
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro Heq.
    destruct Heq.
    apply sUIPt.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
