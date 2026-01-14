From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* For SProp equality, we use the Imported version *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp :=
  @Imported.Corelib_Init_Logic_eq_Prop.

(* Isomorphism for equality on Prop/SProp types *)
(* Since Prop equality is trivial (proof irrelevance) and SProp equality is trivially true, *)
(* we can always establish the isomorphism *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), 
  rel_iso hx x3 x4 -> 
  forall (x5 : x1) (x6 : x2), 
  rel_iso hx x5 x6 -> 
  Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in *.
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 -> Corelib_Init_Logic_eq_Prop x4 x6 *)
    intro Heq.
    destruct Heq.
    (* x3 = x5, so we need x4 = x6. We have H34: to hx x3 = x4, H56: to hx x3 = x6 *)
    (* In SProp, to hx x3 = x4 and to hx x3 = x6, so x4 = x6 (SProp proof irrelevance) *)
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4).
  - (* from: Corelib_Init_Logic_eq_Prop x4 x6 -> x3 = x5 *)
    intro Heq.
    (* Use proof irrelevance: both x3 and x5 are in x1 which maps to SProp x2 *)
    pose (Hfrom34 := from_to hx x3).
    pose (Hfrom56 := from_to hx x5).
    (* H34 : to hx x3 = x4, H56 : to hx x5 = x6 *)
    (* Since x4 and x6 are in SProp, they are equal *)
    assert (Heq_to : IsomorphismDefinitions.eq (to hx x3) (to hx x5)).
    { apply IsomorphismDefinitions.eq_refl. } (* SProp proof irrelevance *)
    pose (step1 := IsoEq.eq_trans (IsoEq.eq_sym Hfrom34) (IsoEq.f_equal (from hx) Heq_to)).
    pose (step2 := IsoEq.eq_trans step1 Hfrom56).
    exact (IsoEq.eq_of_seq step2).
  - (* to_from *)
    intro x.
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to: use UIP *)
    intro Heq.
    destruct Heq.
    apply sUIPt.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) imported_Corelib_Init_Logic_eq_Prop Corelib_Init_Logic_eq_iso_Prop := {}.
