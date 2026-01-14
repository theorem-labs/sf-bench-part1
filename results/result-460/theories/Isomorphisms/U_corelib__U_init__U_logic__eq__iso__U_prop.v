From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

(* eq_iso_Prop: isomorphism for equality on Prop types (maps to SProp on imported side) *)

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For Prop types, equality is always trivial - both sides are in SProp and inhabited *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in *.
  unfold imported_Corelib_Init_Logic_eq_Prop.
  unshelve eapply Build_Iso.
  - (* to: eq in Prop -> imported eq_Prop in SProp *)
    intro Heq.
    (* Corelib_Init_Logic_eq_Prop is just Imported.True *)
    exact Imported.True_intro.
  - (* from: imported eq_Prop in SProp -> eq in Prop *)
    intro Heq.
    (* Since x2 is an SProp, any two elements are equal by proof irrelevance *)
    (* But x1 could be any Type - however hx establishes an iso so x3 and x5 must be related *)
    (* Actually: x4 and x6 are in SProp x2, so to(x3) = x4 and to(x5) = x6 *)
    (* This means from(x4) = x3 and from(x6) = x5 via from_to *)
    (* Also x4 = x6 in SProp by proof irrelevance *)
    (* So from(x4) = from(x6), i.e. x3 = x5 *)
    pose (ft3 := from_to hx x3).
    pose (ft5 := from_to hx x5).
    (* H34 : to x3 = x4, H56 : to x5 = x6 *)
    (* In SProp x2, x4 = x6 definitionally *)
    pose (step1 := IsoEq.f_equal (from hx) H34). (* from(to x3) = from x4 *)
    pose (step2 := IsoEq.f_equal (from hx) H56). (* from(to x5) = from x6 *)
    (* from_to gives: from(to x3) = x3, from(to x5) = x5 *)
    pose (step3 := IsoEq.eq_trans (IsoEq.eq_sym ft3) step1). (* x3 = from x4 *)
    pose (step4 := IsoEq.eq_trans (IsoEq.eq_sym ft5) step2). (* x5 = from x6 *)
    (* In SProp, x4 and x6 are equal, so from x4 = from x6 *)
    (* Actually the issue is we need to show from x4 = from x6 which follows from x4 = x6 in SProp *)
    (* But SProp values are not directly comparable... we use that both x4,x6 : x2 which is SProp *)
    exact (IsoEq.eq_of_seq (IsoEq.eq_trans step3 (IsoEq.eq_sym step4))).
  - (* to_from: both are SProp, so trivially equal *)
    intro Heq.
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to: use UIP for Prop equality *)
    intro Heq.
    destruct Heq.
    apply sUIPt.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
