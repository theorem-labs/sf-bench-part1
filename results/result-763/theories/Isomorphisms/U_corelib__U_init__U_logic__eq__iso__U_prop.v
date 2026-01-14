From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

(* For the Prop case, we use the imported Prop version *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Helper to transport along SProp equality for the Prop version *)
Definition transport_imported_eq_Prop {x2 : SProp} {a b c : x2} 
  (H1 : IsomorphismDefinitions.eq a b) (H2 : IsomorphismDefinitions.eq a c) 
  : Imported.Corelib_Init_Logic_eq_Prop x2 b c.
Proof.
  exact (IsoEq.eq_srect (fun y => Imported.Corelib_Init_Logic_eq_Prop x2 y c)
           (IsoEq.eq_srect (fun z => Imported.Corelib_Init_Logic_eq_Prop x2 a z)
              (Imported.Corelib_Init_Logic_eq_Prop_refl x2 a)
              H2)
           H1).
Defined.

(* The Prop version needs a different argument type *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in *.
  unfold imported_Corelib_Init_Logic_eq_Prop.
  unshelve eapply Build_Iso.
  - (* to *)
    intro Heq.
    destruct Heq.
    (* H34 : to hx x3 = x4, H56 : to hx x3 = x6 *)
    exact (transport_imported_eq_Prop H34 H56).
  - (* from *)
    intro Heq.
    pose (Hfrom34 := from_to hx x3).
    pose (Hfrom56 := from_to hx x5).
    pose (step1 := IsoEq.f_equal (from hx) H34). (* from(to hx x3) = from x4 *)
    pose (step2 := IsoEq.f_equal (from hx) H56). (* from(to hx x5) = from x6 *)
    pose (x4_eq_x6 := Heq). (* x4 = x6 in SProp *)
    (* Use the imported eq eliminator - Heq is now Imported.Corelib_Init_Logic_eq_Prop *)
    pose (from_eq := Imported.Corelib_Init_Logic_eq_Prop_indl x2 x4 
            (fun y _ => IsomorphismDefinitions.eq (from hx x4) (from hx y))
            IsomorphismDefinitions.eq_refl x6 Heq).
    pose (step3 := IsoEq.eq_trans step1 from_eq). (* from(to x3) = from x6 *)
    pose (step4 := IsoEq.eq_trans step3 (IsoEq.eq_sym step2)). (* from(to x3) = from(to x5) *)
    pose (step5 := IsoEq.eq_trans (IsoEq.eq_sym Hfrom34) step4). (* x3 = from(to x5) *)
    pose (step6 := IsoEq.eq_trans step5 Hfrom56). (* x3 = x5 *)
    exact (IsoEq.eq_of_seq step6).
  - (* to_from *)
    intro Heq.
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro Heq.
    destruct Heq.
    apply sUIPt.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
