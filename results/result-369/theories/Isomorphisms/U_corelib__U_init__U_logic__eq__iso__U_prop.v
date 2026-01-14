From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For SProp arguments, the Iso is trivial since SProp values are unique *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in *.
  unshelve eapply Build_Iso.
  - (* to: eq in Prop -> imported eq in SProp *)
    intro Heq.
    destruct Heq.
    (* We have H34: hx x3 = x4 and H56: hx x3 = x6, and we need to prove x4 = x6 *)
    (* Since x4 and x6 are both in SProp, and hx x3 = x4 and hx x3 = x6, 
       we get x4 = x6 by transitivity *)
    pose (Hfromx4 := IsoEq.eq_trans (IsoEq.eq_sym H34) H56).
    exact (IsoEq.eq_srect (fun y => Imported.Corelib_Init_Logic_eq_Prop x2 x4 y)
             (Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4)
             Hfromx4).
  - (* from: imported eq in SProp -> eq in Prop *)
    intro Heq.
    (* H34 : hx x3 = x4, H56 : hx x5 = x6 *)
    (* Heq : imported_Corelib_Init_Logic_eq_Prop x4 x6 (in SProp) *)
    pose (Hfrom34 := from_to hx x3). (* eq (from hx (hx x3)) x3 *)
    pose (Hfrom56 := from_to hx x5). (* eq (from hx (hx x5)) x5 *)
    (* Build from x4 = from x6 using Heq's eliminator into SProp *)
    pose (from_x4_eq_from_x6 := Imported.Corelib_Init_Logic_eq_Prop_indl x2 x4 
            (fun y _ => IsomorphismDefinitions.eq (from hx x4) (from hx y))
            IsomorphismDefinitions.eq_refl x6 Heq).
    (* Now: from(hx x3) = from x4 via H34 *)
    pose (step1 := IsoEq.f_equal (from hx) H34). (* eq (from(hx x3)) (from x4) *)
    (* from x4 = from x6 via from_x4_eq_from_x6 *)
    pose (step2 := IsoEq.eq_trans step1 from_x4_eq_from_x6). (* eq (from(hx x3)) (from x6) *)
    (* from x6 = from(hx x5) via eq_sym H56 *)
    pose (step3 := IsoEq.f_equal (from hx) (IsoEq.eq_sym H56)). (* eq (from x6) (from(hx x5)) *)
    pose (step4 := IsoEq.eq_trans step2 step3). (* eq (from(hx x3)) (from(hx x5)) *)
    (* from(hx x3) = x3 via Hfrom34, from(hx x5) = x5 via Hfrom56 *)
    pose (step5 := IsoEq.eq_trans (IsoEq.eq_sym Hfrom34) step4). (* eq x3 (from(hx x5)) *)
    pose (step6 := IsoEq.eq_trans step5 Hfrom56). (* eq x3 x5 *)
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
