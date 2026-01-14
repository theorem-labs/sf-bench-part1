From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

(* For Prop arguments, the imported equality is also over SProp *)
(* Since Type gets imported as Type and Prop gets imported as SProp,
   Corelib_Init_Logic_eq (which works for Type) needs a Prop variant *)
   
(* The Prop variant expects SProp arguments - use the imported version *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := 
  @Imported.Corelib_Init_Logic_eq_Prop.

(* Helper to transport between SProp equalities *)
Definition transport_eq_Prop {A : SProp} {a b c : A} 
  (H1 : IsomorphismDefinitions.eq a b) (H2 : IsomorphismDefinitions.eq a c) 
  : Imported.Corelib_Init_Logic_eq_Prop A b c.
Proof.
  exact (IsoEq.eq_srect (fun y => Imported.Corelib_Init_Logic_eq_Prop A y c)
           (IsoEq.eq_srect (fun z => Imported.Corelib_Init_Logic_eq_Prop A a z)
              (Imported.Corelib_Init_Logic_eq_Prop_refl A a)
              H2)
           H1).
Defined.

(* Isomorphism for eq over Prop (which gets mapped to SProp) *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), 
  rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> 
  Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in *.
  unfold imported_Corelib_Init_Logic_eq_Prop.
  (* Build directly using the fact that x3 = x5 is a Prop and eq x4 x6 is SProp *)
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 in Prop -> Imported.Corelib_Init_Logic_eq_Prop x2 x4 x6 in SProp *)
    intro Heq.
    destruct Heq.
    exact (transport_eq_Prop H34 H56).
  - (* from: Imported.Corelib_Init_Logic_eq_Prop x2 x4 x6 in SProp -> x3 = x5 in Prop *)
    intro Heq.
    (* Use the imported eliminator *)
    pose (from_x4_eq_from_x6 := Imported.Corelib_Init_Logic_eq_Prop_indl x2 x4 
            (fun y _ => IsomorphismDefinitions.eq (from hx x4) (from hx y))
            IsomorphismDefinitions.eq_refl x6 Heq).
    pose (Hfrom34 := from_to hx x3).
    pose (Hfrom56 := from_to hx x5).
    pose (step1 := IsoEq.f_equal (from hx) H34). (* from(hx x3) = from x4 *)
    pose (step2 := IsoEq.eq_trans step1 from_x4_eq_from_x6). (* from(hx x3) = from x6 *)
    pose (step3 := IsoEq.f_equal (from hx) (IsoEq.eq_sym H56)). (* from x6 = from(hx x5) *)
    pose (step4 := IsoEq.eq_trans step2 step3). (* from(hx x3) = from(hx x5) *)
    pose (step5 := IsoEq.eq_trans (IsoEq.eq_sym Hfrom34) step4). (* x3 = from(hx x5) *)
    pose (step6 := IsoEq.eq_trans step5 Hfrom56). (* x3 = x5 *)
    exact (IsoEq.eq_of_seq step6).
  - (* to_from: target is SProp, trivial *)
    intro. apply IsomorphismDefinitions.eq_refl.
  - (* from_to: source is Prop, use proof irrelevance *)
    intro Heq. destruct Heq. apply sUIPt.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
