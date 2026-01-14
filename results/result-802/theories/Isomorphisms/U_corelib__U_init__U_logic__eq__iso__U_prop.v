From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* For SProp, all elements are equal - use the imported definition which is always True *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := 
  @Imported.Corelib_Init_Logic_eq_Prop.

(* For SProp arguments, we can use SProp proof irrelevance *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in *.
  unshelve eapply Build_Iso.
  - (* to: eq in Prop -> imported eq_Prop in SProp *)
    intro Heq.
    destruct Heq.
    (* Both H34 and H56 relate x3 to x4 and x5 to x6 respectively *)
    (* Since imported_Corelib_Init_Logic_eq_Prop is True, trivially inhabited *)
    unfold imported_Corelib_Init_Logic_eq_Prop.
    exact Imported.True_intro.
  - (* from: imported eq_Prop in SProp -> eq in Prop *)
    intro Heq.
    (* H34 : to hx x3 = x4, H56 : to hx x5 = x6 *)
    (* We need to show x3 = x5 *)
    pose (Hfrom34 := from_to hx x3). (* eq (from hx (to hx x3)) x3 *)
    pose (Hfrom56 := from_to hx x5). (* eq (from hx (to hx x5)) x5 *)
    (* Since x4, x6 are in SProp, from hx x4 = from hx x6 in SProp *)
    (* We know from hx x4 = from (to hx x3) = x3 and from hx x6 = from (to hx x5) = x5 *)
    (* x4 and x6 are in SProp, so from hx x4 = from hx x6 due to SProp equality *)
    (* But we can use the transport: from x4 = from(to hx x3), from x6 = from(to hx x5) *)
    (* Actually, in SProp all proofs are equal, so to hx x3 = x4 = x6 = to hx x5 *)
    (* Therefore from(to hx x3) = from(to hx x5), i.e., x3 = x5 *)
    (* Use SProp proof irrelevance directly *)
    pose (step1 := IsoEq.f_equal (from hx) H34). (* eq (from(to hx x3)) (from x4) *)
    pose (step2 := IsoEq.f_equal (from hx) (IsoEq.eq_sym H56)). (* eq (from x6) (from(to hx x5)) *)
    (* In SProp, x4 = x6, so from hx x4 = from hx x6 *)
    assert (from_eq : IsomorphismDefinitions.eq (from hx x4) (from hx x6)) by exact IsomorphismDefinitions.eq_refl.
    pose (step3 := IsoEq.eq_trans step1 from_eq). (* eq (from(to hx x3)) (from x6) *)
    pose (step4 := IsoEq.eq_trans step3 step2). (* eq (from(to hx x3)) (from(to hx x5)) *)
    pose (step5 := IsoEq.eq_trans (IsoEq.eq_sym Hfrom34) step4). (* eq x3 (from(to hx x5)) *)
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
Instance: KnownConstant (@imported_Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@imported_Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
