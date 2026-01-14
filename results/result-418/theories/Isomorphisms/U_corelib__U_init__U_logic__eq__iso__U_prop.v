From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For Prop types, both source and target are SProp after import *)
(* Since both sides are in SProp, proof irrelevance gives us the isomorphism trivially *)
(* The key insight: when x2 is an SProp, x4 and x6 are irrelevant, so eq_Prop x4 x6 is trivially true *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2),
  rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> 
  Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in *.
  unfold imported_Corelib_Init_Logic_eq_Prop.
  unshelve eapply Build_Iso.
  - (* to: eq in Prop -> imported eq_Prop in SProp *)
    intro Heq.
    destruct Heq.
    (* We have H34: to hx x3 = x4 and H56: to hx x3 = x6 *)
    (* Need to prove Imported.Corelib_Init_Logic_eq_Prop x4 x6 in SProp *)
    (* Since x2 is an SProp and x4, x6 : x2, we have x4 = x6 by SProp proof irrelevance *)
    (* So we can use refl *)
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4).
  - (* from: imported eq_Prop in SProp -> eq in Prop *)
    intro Heq.
    (* Both x4 and x6 are in SProp x2 *)
    (* Heq : Imported.Corelib_Init_Logic_eq_Prop x4 x6 in SProp *)
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
  - (* to_from: both are SProp *)
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
