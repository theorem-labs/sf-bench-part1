From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Equality for Props (SProp on imported side) *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* When both arguments are in Prop (which becomes SProp), equality between 
   inhabitants is trivial since all inhabitants of an SProp are equal *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in *.
  unfold imported_Corelib_Init_Logic_eq_Prop.
  (* x3 = x5 is a Prop, Imported.Corelib_Init_Logic_eq_Prop x4 x6 is SProp *)
  (* The imported eq_Prop is defined as True_, so it's always inhabited *)
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 -> imported eq_Prop in SProp *)
    intro Heq.
    (* Imported.Corelib_Init_Logic_eq_Prop is True (always True_) *)
    exact Imported.True_I.
  - (* from: imported eq_Prop in SProp -> x3 = x5 *)
    intro Hsi.
    (* from hx x4 = from hx x6 because x4, x6 : SProp are definitionally equal *)
    (* But we have hx : Iso x1 x2 where x2 : SProp *)
    (* Since x2 is an SProp, all its elements are equal, so x4 = x6 *)
    (* Therefore from hx x4 = from hx x6 *)
    (* And by from_to: from (to x3) = x3, from (to x5) = x5 *)
    (* By H34: to x3 = x4, H56: to x5 = x6 *)
    (* So from x4 = x3, from x6 = x5 *)
    (* Since x4 = x6 (SProp), we have x3 = x5 *)
    pose proof (from_to hx x3) as FT3.
    pose proof (from_to hx x5) as FT5.
    (* from hx x4 = x3 via H34 and from_to *)
    pose proof (@IsomorphismDefinitions.eq_rect x2 (to hx x3)
      (fun y _ => from hx y = x3) 
      (@IsomorphismDefinitions.eq_rect x1 (from hx (to hx x3))
        (fun y _ => from hx (to hx x3) = y) 
        (@Corelib.Init.Logic.eq_refl x1 (from hx (to hx x3))) x3 FT3)
      x4 H34) as HX3.
    (* from hx x6 = x5 via H56 and from_to *)
    pose proof (@IsomorphismDefinitions.eq_rect x2 (to hx x5)
      (fun y _ => from hx y = x5) 
      (@IsomorphismDefinitions.eq_rect x1 (from hx (to hx x5))
        (fun y _ => from hx (to hx x5) = y) 
        (@Corelib.Init.Logic.eq_refl x1 (from hx (to hx x5))) x5 FT5)
      x6 H56) as HX5.
    (* Since x2 : SProp, x4 and x6 are definitionally equal *)
    (* So from hx x4 = from hx x6 *)
    assert (from hx x4 = from hx x6) as Heq by reflexivity.
    (* Combine: x3 = from x4 = from x6 = x5 *)
    exact (Corelib.Init.Logic.eq_trans 
           (Corelib.Init.Logic.eq_sym HX3) 
           (Corelib.Init.Logic.eq_trans Heq HX5)).
  - (* to_from: SProp equality *)
    intro Hsi.
    (* Both sides are in SProp, so definitionally equal *)
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to: use proof irrelevance *)
    intro Heq.
    apply sUIPt.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
