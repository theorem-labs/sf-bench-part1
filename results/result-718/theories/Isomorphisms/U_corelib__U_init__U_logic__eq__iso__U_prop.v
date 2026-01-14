From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

(* Now the Prop version for SProp arguments *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* When x2 : SProp, we need an iso between (x3 = x5) and (imported_Corelib_Init_Logic_eq_Prop x4 x6) *)
(* Both are in SProp (the imported one explicitly, and the original eq in Prop maps to SProp via SInhabited) *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in *.
  (* Build the isomorphism directly *)
  unshelve eapply Build_Iso.
  - (* to: (x3 = x5) -> imported_Corelib_Init_Logic_eq_Prop x4 x6 *)
    intro Heq.
    destruct Heq.
    (* Now x5 = x3, so we have H34 : eq (hx x3) x4 and H56 : eq (hx x3) x6 *)
    (* Since x4 x6 : x2 : SProp, they are equal by SProp irrelevance *)
    (* But we need to build Corelib_Init_Logic_eq_Prop x4 x6 *)
    (* Actually, we don't have a way to prove x4 = x6 in SProp directly from H34 and H56 unless... *)
    (* Wait, H34 and H56 are in IsomorphismDefinitions.eq which is SProp *)
    (* We can use the fact that both are SProp to get that x4 = x6 *)
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4).
  - (* from: imported_Corelib_Init_Logic_eq_Prop x4 x6 -> (x3 = x5) *)
    intro Heq.
    (* Use from_to to get back x3 and x5 *)
    pose (Hfrom34 := from_to hx x3).
    pose (Hfrom56 := from_to hx x5).
    (* Now use H34 : eq (hx x3) x4, H56 : eq (hx x5) x6 *)
    (* We need to show x3 = x5 *)
    (* from hx x4 = from hx (hx x3) = x3 by Hfrom34 and f_equal *)
    (* Similarly for x5 *)
    (* We can use the Heq to get from x4 = from x6 in SProp *)
    pose (from_eq := Imported.Corelib_Init_Logic_eq_Prop_indl x2 x4 
            (fun y _ => IsomorphismDefinitions.eq (from hx x4) (from hx y))
            IsomorphismDefinitions.eq_refl x6 Heq).
    pose (step1 := IsoEq.f_equal (from hx) H34). (* eq (from (hx x3)) (from x4) *)
    pose (step2 := IsoEq.eq_trans step1 from_eq). (* eq (from (hx x3)) (from x6) *)
    pose (step3 := IsoEq.f_equal (from hx) (IsoEq.eq_sym H56)). (* eq (from x6) (from (hx x5)) *)
    pose (step4 := IsoEq.eq_trans step2 step3). (* eq (from (hx x3)) (from (hx x5)) *)
    pose (step5 := IsoEq.eq_trans (IsoEq.eq_sym Hfrom34) step4). (* eq x3 (from (hx x5)) *)
    pose (step6 := IsoEq.eq_trans step5 Hfrom56). (* eq x3 x5 *)
    exact (IsoEq.eq_of_seq step6).
  - (* to_from: both are in SProp *)
    intro Heq.
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to: use UIP *)
    intro Heq.
    destruct Heq.
    apply sUIPt.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) imported_Corelib_Init_Logic_eq_Prop Corelib_Init_Logic_eq_iso_Prop := {}.
