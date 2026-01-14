From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For Prop types, since they get mapped to SProp and all SProp values are equal,
   this isomorphism is trivial *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold imported_Corelib_Init_Logic_eq_Prop.
  unfold rel_iso in *.
  (* x3 = x5 in Prop, Corelib_Init_Logic_eq_Prop x2 x4 x6 = True in SProp *)
  unshelve eapply Build_Iso.
  - (* to: (x3 = x5) -> Imported.Corelib_Init_Logic_eq_Prop x2 x4 x6 *)
    intro Heq. exact Imported.True_intro.
  - (* from: Imported.Corelib_Init_Logic_eq_Prop x2 x4 x6 -> (x3 = x5) *)
    intro Hignored.
    (* H34 : hx x3 = x4, H56 : hx x5 = x6 *)
    pose (Hfrom34 := from_to hx x3). (* eq (from hx (hx x3)) x3 *)
    pose (Hfrom56 := from_to hx x5). (* eq (from hx (hx x5)) x5 *)
    (* We need to show x3 = x5, but we have no actual equality evidence between x4 and x6 *)
    (* Since x2 is SProp, all elements are equal, so we can derive from hx x3 = from hx x5 *)
    (* But from : x2 -> x1 and x2 is SProp, so from x4 = from x6 since x4 and x6 are in SProp *)
    assert (Heq_from : IsomorphismDefinitions.eq (from hx x4) (from hx x6)).
    { apply IsomorphismDefinitions.eq_refl. (* SProp proof irrelevance *) }
    pose (step1 := IsoEq.f_equal (from hx) H34). (* from(hx x3) = from x4 *)
    pose (step2 := IsoEq.f_equal (from hx) H56). (* from(hx x5) = from x6 *)
    pose (step3 := IsoEq.eq_trans (IsoEq.eq_sym Hfrom34) step1). (* x3 = from x4 *)
    pose (step4 := IsoEq.eq_trans (IsoEq.eq_sym Hfrom56) step2). (* x5 = from x6 *)
    pose (step5 := IsoEq.eq_trans step3 Heq_from). (* x3 = from x6 *)
    pose (step6 := IsoEq.eq_trans step5 (IsoEq.eq_sym step4)). (* x3 = x5 *)
    exact (IsoEq.eq_of_seq step6).
  - (* to_from: SProp so trivial *)
    intro x. apply IsomorphismDefinitions.eq_refl.
  - (* from_to: use UIP for Prop equality *)
    intro x. apply sUIPt.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
