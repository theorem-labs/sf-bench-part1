From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in *.
  unshelve eapply Build_Iso.
  - (* to: eq x3 x5 -> imported_Corelib_Init_Logic_eq_Prop x4 x6 *)
    intro Heq.
    (* Both x4 and x6 are in SProp, so equality in SProp is trivial *)
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4).
  - (* from: imported_Corelib_Init_Logic_eq_Prop x4 x6 -> eq x3 x5 *)
    intro Heq.
    (* x1 : Type with Iso x1 x2 where x2 : SProp *)
    (* This means x1 is effectively Prop-like *)
    (* Since x2 is SProp, use proof irrelevance on x1 *)
    destruct Heq.
    (* Now we have reflexivity in the imported eq *)
    (* Build eq x3 x5 using the fact that from respects SProp equality *)
    pose (Hfrom34 := from_to hx x3).
    pose (Hfrom56 := from_to hx x5).
    (* x4 = x6 in SProp is trivial, so from x4 = from x6 *)
    (* But x3 = from (to x3), x5 = from (to x5) *)
    pose (step1 := IsoEq.eq_trans (IsoEq.eq_sym Hfrom34) Hfrom56).
    exact (IsoEq.eq_of_seq step1).
  - (* to_from *)
    intro Heq.
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro Heq.
    destruct Heq.
    apply sUIPt.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
