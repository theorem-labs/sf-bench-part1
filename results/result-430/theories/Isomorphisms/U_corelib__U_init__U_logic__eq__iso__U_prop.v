From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

(* Eq for Prop types - SProp equality on SProp elements *)
(* For SProp inhabitants, all elements are equal, so we return True *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := 
  Imported.Corelib_Init_Logic_eq_Prop.

Instance Corelib_Init_Logic_eq_iso_Prop : 
  forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), 
    rel_iso hx x3 x4 -> 
    forall (x5 : x1) (x6 : x2), 
      rel_iso hx x5 x6 -> 
      Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold imported_Corelib_Init_Logic_eq_Prop.
  unshelve eapply Build_Iso.
  - (* to: eq in Prop -> Imported.True (SProp) *)
    intro Heq. exact Imported.True_intro.
  - (* from: Imported.True -> eq in Prop *)
    intro Htrue.
    unfold rel_iso in *.
    (* x4 and x6 are in SProp x2, so they are definitionally equal *)
    (* from_to hx x3 : eq (from hx (hx x3)) x3 *)
    (* from_to hx x5 : eq (from hx (hx x5)) x5 *)
    (* Since x4 and x6 are in SProp, from hx x4 = from hx x6 *)
    (* We need to show x3 = x5 *)
    (* x3 = from(to x3) = from x4 = from x6 = from(to x5) = x5 *)
    pose (step1 := from_to hx x3). (* eq (from hx (hx x3)) x3 *)
    pose (step2 := from_to hx x5). (* eq (from hx (hx x5)) x5 *)
    (* Since x4 : x2 and x6 : x2 where x2 : SProp, we have from hx x4 = from hx x6 definitionally *)
    (* Actually we need f_equal from H34 and H56 *)
    pose (Hfrom4 := IsoEq.f_equal (from hx) H34). (* eq (from(to x3)) (from x4) *)
    pose (Hfrom6 := IsoEq.f_equal (from hx) H56). (* eq (from(to x5)) (from x6) *)
    (* Since x4, x6 : SProp x2, they are equal in SProp, so from x4 = from x6 *)
    (* In SProp, all terms are definitionally equal, so from hx x4 ≡ from hx x6 *)
    pose (step3 := IsoEq.eq_trans (IsoEq.eq_sym step1) Hfrom4). (* eq x3 (from x4) *)
    pose (step4 := IsoEq.eq_trans (IsoEq.eq_sym step2) Hfrom6). (* eq x5 (from x6) *)
    (* from x4 = from x6 because x4, x6 : SProp *)
    exact (IsoEq.eq_of_seq (IsoEq.eq_trans step3 (IsoEq.eq_sym step4))).
  - (* to_from: Imported.True is SProp, so any two proofs are equal *)
    intro Htrue. apply IsomorphismDefinitions.eq_refl.
  - (* from_to: Prop UIP *)
    intro Heq. destruct Heq. apply sUIPt.
Defined.

Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) imported_Corelib_Init_Logic_eq_Prop Corelib_Init_Logic_eq_iso_Prop := {}.
