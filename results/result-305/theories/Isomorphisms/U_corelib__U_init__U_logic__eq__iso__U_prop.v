From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall (x : SProp), x -> x -> SProp := fun x => @Imported.Corelib_Init_Logic_eq_Prop x.

(* For Prop-sorted types, we go from Type (x1) to SProp (x2) *)
(* The original equality is on x3, x5 : x1 (Type) *)
(* The imported equality is on x4, x6 : x2 (SProp) *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in *.
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 (Prop) -> x4 = x6 (SProp) *)
    intro Heq.
    destruct Heq.
    (* x3 = x3 implies we need x4 = x6 *)
    (* H34 : to(x3) = x4, H56 : to(x3) = x6 *)
    exact (eq_srect (fun y => Imported.Corelib_Init_Logic_eq_Prop x2 y x6)
             (eq_srect (fun z => Imported.Corelib_Init_Logic_eq_Prop x2 (to hx x3) z)
                (Imported.Corelib_Init_Logic_eq_Prop_refl x2 (to hx x3))
                H56)
             H34).
  - (* from: x4 = x6 (SProp) -> x3 = x5 (Prop) *)
    intro Heq.
    (* H34 : to(x3) = x4, H56: to(x5) = x6 *)
    (* Heq : x4 = x6 in SProp *)
    (* We use Imported.Corelib_Init_Logic_eq_Prop_indl to transport *)
    pose (from_x4_eq_from_x6 := Imported.Corelib_Init_Logic_eq_Prop_indl x2 x4 
            (fun y _ => IsomorphismDefinitions.eq (from hx x4) (from hx y))
            IsomorphismDefinitions.eq_refl x6 Heq).
    pose (step1 := IsoEq.f_equal (from hx) H34). (* eq (from(to x3)) (from x4) *)
    pose (step2 := IsoEq.eq_trans step1 from_x4_eq_from_x6). (* eq (from(to x3)) (from x6) *)
    pose (step3 := IsoEq.f_equal (from hx) (IsoEq.eq_sym H56)). (* eq (from x6) (from(to x5)) *)
    pose (step4 := IsoEq.eq_trans step2 step3). (* eq (from(to x3)) (from(to x5)) *)
    pose (step5 := IsoEq.eq_trans (IsoEq.eq_sym (from_to hx x3)) step4). (* eq x3 (from(to x5)) *)
    pose (step6 := IsoEq.eq_trans step5 (from_to hx x5)). (* eq x3 x5 *)
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
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
