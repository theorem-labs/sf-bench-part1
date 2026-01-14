From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

(* We don't import U_true__iso because it's not actually used *)
(* The dependency is only in the Interface file structure *)

Definition imported_Corelib_Init_Logic_eq : forall x : Type, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq.

(* Helper to transport along SProp equality - now the target is also SProp *)
Definition transport_imported_eq {x2 : Type} {a b c : x2} 
  (H1 : IsomorphismDefinitions.eq a b) (H2 : IsomorphismDefinitions.eq a c) 
  : Imported.Corelib_Init_Logic_eq x2 b c.
Proof.
  exact (IsoEq.eq_srect (fun y => Imported.Corelib_Init_Logic_eq x2 y c)
           (IsoEq.eq_srect (fun z => Imported.Corelib_Init_Logic_eq x2 a z)
              (Imported.Corelib_Init_Logic_eq_refl x2 a)
              H2)
           H1).
Defined.

(* Both equalities are now in SProp-like (Prop for original, SProp for imported) *)
Instance Corelib_Init_Logic_eq_iso : (forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in *.
  unshelve eapply Build_Iso.
  - (* to: eq in Prop -> imported eq in SProp *)
    intro Heq.
    destruct Heq.
    (* We have H34: hx x3 = x4 and H56: hx x3 = x6, and we need to prove x4 = x6 *)
    exact (transport_imported_eq H34 H56).
  - (* from: imported eq in SProp -> eq in Prop *)
    intro Heq.
    (* H34 : hx x3 = x4, H56 : hx x5 = x6 *)
    (* Heq : imported_Corelib_Init_Logic_eq x4 x6 (in SProp) *)
    (* Use the imported eq eliminator (indl) to build from x4 = from x6 *)
    pose (Hfrom34 := from_to hx x3). (* eq (from hx (hx x3)) x3 *)
    pose (Hfrom56 := from_to hx x5). (* eq (from hx (hx x5)) x5 *)
    (* Build from x4 = from x6 using Heq's eliminator into SProp *)
    pose (from_x4_eq_from_x6 := Imported.Corelib_Init_Logic_eq_indl x2 x4 
            (fun y _ => IsomorphismDefinitions.eq (from hx x4) (from hx y))
            IsomorphismDefinitions.eq_refl x6 Heq).
    (* Now: from(hx x3) = from x4 via H34 *)
    pose (step1 := IsoEq.f_equal (from hx) H34). (* eq (from(hx x3)) (from x4) *)
    (* from x4 = from x6 via from_x4_eq_from_x6 *)
    pose (step2 := IsoEq.eq_trans step1 from_x4_eq_from_x6). (* eq (from(hx x3)) (from x6) *)
    (* from x6 = from(hx x5) via eq_sym H56 *)
    pose (step3 := IsoEq.f_equal (from hx) (IsoEq.eq_sym H56)). (* eq (from x6) (from(hx x5)) *)
    pose (step4 := IsoEq.eq_trans step2 step3). (* eq (from(hx x3)) (from(hx x5)) *)
    (* from(hx x3) = x3 via Hfrom34, from(hx x5) = x5 via Hfrom56 *)
    pose (step5 := IsoEq.eq_trans (IsoEq.eq_sym Hfrom34) step4). (* eq x3 (from(hx x5)) *)
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
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq) Corelib_Init_Logic_eq_iso := {}.

(* Also provide the _Prop variant for SProp first argument *)
(* Use WrapSProp to lift SProp to Type *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := 
  fun (x : SProp) (a b : x) => @Imported.Corelib_Init_Logic_eq (WrapSProp x) {| unwrap_sprop := a |} {| unwrap_sprop := b |}.

Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), 
  rel_iso hx x3 x4 -> 
  forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> 
  Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold imported_Corelib_Init_Logic_eq_Prop.
  (* Build an iso using the same approach as the Type variant *)
  unshelve eapply Build_Iso.
  - intro Heq. destruct Heq.
    apply Imported.Corelib_Init_Logic_eq_refl.
  - intro Heq.
    apply (IsoEq.eq_of_seq).
    pose proof (from_to hx x3) as Hfrom3.
    pose proof (from_to hx x5) as Hfrom5.
    pose (from_x4_eq_from_x6 := Imported.Corelib_Init_Logic_eq_indl (WrapSProp x2) {| unwrap_sprop := x4 |}
            (fun y _ => IsomorphismDefinitions.eq (from hx x4) (from hx (unwrap_sprop y)))
            IsomorphismDefinitions.eq_refl {| unwrap_sprop := x6 |} Heq).
    pose (step1 := IsoEq.f_equal (from hx) H34).
    pose (step2 := IsoEq.eq_trans step1 from_x4_eq_from_x6).
    pose (step3 := IsoEq.f_equal (from hx) (IsoEq.eq_sym H56)).
    pose (step4 := IsoEq.eq_trans step2 step3).
    pose (step5 := IsoEq.eq_trans (IsoEq.eq_sym Hfrom3) step4).
    pose (step6 := IsoEq.eq_trans step5 Hfrom5).
    exact step6.
  - intro Heq. apply IsomorphismDefinitions.eq_refl.
  - intro Heq. destruct Heq. apply sUIPt.
Defined.

Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) imported_Corelib_Init_Logic_eq_Prop Corelib_Init_Logic_eq_iso_Prop := {}.

(* Re-export the __U_prop module *)
From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso__U_prop.
