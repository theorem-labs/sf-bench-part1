From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For SProp -> SProp -> SProp equality, all elements are equal, so this is trivial *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  (* Both sides are propositions - x3 = x5 is Prop, imported_Corelib_Init_Logic_eq_Prop x4 x6 is SProp *)
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 -> imported_Corelib_Init_Logic_eq_Prop x4 x6 *)
    intro Heq.
    unfold imported_Corelib_Init_Logic_eq_Prop.
    exact Imported.True_intro.
  - (* from: imported_Corelib_Init_Logic_eq_Prop x4 x6 -> x3 = x5 *)
    intro Himported.
    (* Since x1 is inhabited (via hx and x3), and we have an Iso x1 x2 where x2 : SProp *)
    (* All elements of SProp are equal, so from hx x3 = x4 and from hx x5 = x6 *)
    (* and all SProp elements are equal, we need to derive x3 = x5 *)
    unfold rel_iso in *.
    (* H34 : to hx x3 = x4, H56 : to hx x5 = x6 *)
    (* We need: x3 = x5 *)
    pose proof (from_to hx x3) as H3.
    pose proof (from_to hx x5) as H5.
    (* H3 : from hx (to hx x3) = x3 *)
    (* H5 : from hx (to hx x5) = x5 *)
    (* Since x2 : SProp, to hx x3 = to hx x5 (all SProp elements are equal) *)
    (* Therefore from hx (to hx x3) = from hx (to hx x5) *)
    (* Therefore x3 = x5 *)
    assert (Heq_to : IsomorphismDefinitions.eq (to hx x3) (to hx x5)) by apply IsomorphismDefinitions.eq_refl.
    pose proof (IsoEq.f_equal (from hx) Heq_to) as Heq_from.
    pose proof (IsoEq.eq_trans (IsoEq.eq_sym H3) Heq_from) as step1.
    pose proof (IsoEq.eq_trans step1 H5) as step2.
    exact (IsoEq.eq_of_seq step2).
  - (* to_from *)
    intro Himported.
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro Heq.
    apply sUIPt.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
