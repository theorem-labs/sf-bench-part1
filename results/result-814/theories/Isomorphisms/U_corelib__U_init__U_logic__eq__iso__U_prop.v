From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For SProp equality, both sides are proof irrelevant *)
(* Since x2 is SProp, x4 and x6 are definitionally equal (proof irrelevance) *)
(* So imported_Corelib_Init_Logic_eq_Prop x4 x6 = imported_Corelib_Init_Logic_eq_Prop x4 x4 which is inhabited by refl *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in *.
  unfold imported_Corelib_Init_Logic_eq_Prop.
  unshelve eapply Build_Iso.
  - (* to: (x3 = x5) -> Imported.Corelib_Init_Logic_eq_Prop x2 x4 x6 *)
    intro Heq.
    (* In SProp, x4 and x6 are definitionally equal, so just use refl *)
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4).
  - (* from: Imported.Corelib_Init_Logic_eq_Prop x2 x4 x6 -> (x3 = x5) *)
    intro Heq.
    (* H34 : to hx x3 = x4, H56 : to hx x5 = x6 (in SProp) *)
    (* In SProp, x4 = x6 definitionally, so to hx x3 = to hx x5 *)
    (* But we need x3 = x5 in Prop *)
    (* Use from_to: from(to x3) = x3, from(to x5) = x5 *)
    pose (Hfrom34 := from_to hx x3). (* eq (from hx (to hx x3)) x3 *)
    pose (Hfrom56 := from_to hx x5). (* eq (from hx (to hx x5)) x5 *)
    (* Since x4 = x6 definitionally in SProp, from x4 = from x6 definitionally *)
    (* And from(to x3) = from x4 via H34, from(to x5) = from x6 via H56 *)
    (* So from(to x3) = from(to x5) *)
    pose (step1 := IsoEq.f_equal (from hx) H34). (* from(to x3) = from x4 *)
    pose (step2 := IsoEq.f_equal (from hx) H56). (* from(to x5) = from x6 *)
    (* In SProp, x4 = x6, so from x4 = from x6 by reflexivity *)
    (* step1: from(to x3) = from x4, step2: from(to x5) = from x6 = from x4 *)
    pose (step3 := IsoEq.eq_trans step1 (IsoEq.eq_sym step2)). (* from(to x3) = from(to x5) *)
    pose (step4 := IsoEq.eq_trans (IsoEq.eq_sym Hfrom34) step3). (* x3 = from(to x5) *)
    pose (step5 := IsoEq.eq_trans step4 Hfrom56). (* x3 = x5 *)
    exact (eq_of_seq step5).
  - (* to_from: SProp equality is proof-irrelevant *)
    intro Heq.
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to: use UIP for Prop equality *)
    intro Heq.
    apply sUIPt.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
