From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Use the imported Corelib_Init_Logic_eq_Prop directly - after manual edit, it has the right type *)
(* Interface expects: forall x : SProp, x -> x -> SProp *)
(* Imported has: forall A : SProp, A -> A -> SProp (after manual .out edit) *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := 
  @Imported.Corelib_Init_Logic_eq_Prop.

(* Isomorphism between eq at Prop and imported eq at SProp *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in *.
  unshelve eapply Build_Iso.
  - (* to: eq in Prop -> imported eq_Prop in SProp *)
    intro Heq.
    destruct Heq.
    unfold imported_Corelib_Init_Logic_eq_Prop.
    (* We need: Imported.Corelib_Init_Logic_eq_Prop x2 x4 x6 *)
    (* In SProp, all elements are equal, so we just need reflexivity *)
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4).
  - (* from: imported eq_Prop in SProp -> eq in Prop *)
    intro Heq.
    unfold imported_Corelib_Init_Logic_eq_Prop in Heq.
    (* Heq : Imported.Corelib_Init_Logic_eq_Prop x2 x4 x6 *)
    pose proof (from_to hx x3) as FT3.
    pose proof (from_to hx x5) as FT5.
    (* from hx x4 = x3 *)
    pose proof (@IsomorphismDefinitions.eq_rect x2 (to hx x3)
      (fun y _ => from hx y = x3) 
      (@IsomorphismDefinitions.eq_rect x1 (from hx (to hx x3))
        (fun y _ => from hx (to hx x3) = y) 
        (@Corelib.Init.Logic.eq_refl x1 (from hx (to hx x3))) x3 FT3)
      x4 H34) as HX3.
    (* from hx x6 = x5 *)
    pose proof (@IsomorphismDefinitions.eq_rect x2 (to hx x5)
      (fun y _ => from hx y = x5) 
      (@IsomorphismDefinitions.eq_rect x1 (from hx (to hx x5))
        (fun y _ => from hx (to hx x5) = y) 
        (@Corelib.Init.Logic.eq_refl x1 (from hx (to hx x5))) x5 FT5)
      x6 H56) as HX5.
    (* from hx x4 = from hx x6 via the eliminator *)
    pose proof (Imported.Corelib_Init_Logic_eq_Prop_recl x2 x4 
      (fun z _ => from hx x4 = from hx z) 
      (@Corelib.Init.Logic.eq_refl x1 (from hx x4)) x6 Heq) as Hfrom.
    exact (Corelib.Init.Logic.eq_trans 
           (Corelib.Init.Logic.eq_sym HX3) 
           (Corelib.Init.Logic.eq_trans Hfrom HX5)).
  - (* to_from *)
    intro Heq.
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro Heq.
    destruct Heq.
    apply sUIPt.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
