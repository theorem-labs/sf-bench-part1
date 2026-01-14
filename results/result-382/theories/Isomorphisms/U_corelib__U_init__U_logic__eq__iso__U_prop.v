From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For SProp, we build the isomorphism directly *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 -> imported_Corelib_Init_Logic_eq_Prop x4 x6 *)
    intro Heq.
    destruct Heq.
    unfold imported_Corelib_Init_Logic_eq_Prop, Imported.Corelib_Init_Logic_eq_Prop.
    (* Need to prove eq'_Prop x4 x6, i.e., eq'_Prop (to hx x3) x6 *)
    (* In SProp, x4 and x6 are definitionally equal if they're both in the same SProp *)
    exact (Imported.eq'_Prop_refl x2 x4).
  - (* from: imported_Corelib_Init_Logic_eq_Prop x4 x6 -> x3 = x5 *)
    intro Heq.
    pose proof (from_to hx x3) as FT3.
    pose proof (from_to hx x5) as FT5.
    pose proof (@IsomorphismDefinitions.eq_rect x2 (to hx x3)
      (fun y _ => from hx y = x3) 
      (@IsomorphismDefinitions.eq_rect x1 (from hx (to hx x3))
        (fun y _ => from hx (to hx x3) = y) 
        (@Corelib.Init.Logic.eq_refl x1 (from hx (to hx x3))) x3 FT3)
      x4 H34) as HX3.
    pose proof (@IsomorphismDefinitions.eq_rect x2 (to hx x5)
      (fun y _ => from hx y = x5) 
      (@IsomorphismDefinitions.eq_rect x1 (from hx (to hx x5))
        (fun y _ => from hx (to hx x5) = y) 
        (@Corelib.Init.Logic.eq_refl x1 (from hx (to hx x5))) x5 FT5)
      x6 H56) as HX5.
    (* Use eq'_Prop_recl to get from hx x4 = from hx x6 *)
    pose proof (Imported.eq'_Prop_recl x2 x4 
      (fun z _ => from hx x4 = from hx z) 
      (@Corelib.Init.Logic.eq_refl x1 (from hx x4)) x6 Heq) as Hfrom.
    exact (Corelib.Init.Logic.eq_trans 
           (Corelib.Init.Logic.eq_sym HX3) 
           (Corelib.Init.Logic.eq_trans Hfrom HX5)).
  - (* to_from: SProp proof irrelevance *)
    intro Heq.
    apply (Imported.eq'_Prop_indl x2 x4 
      (fun z pf => IsomorphismDefinitions.eq _ pf) 
      IsomorphismDefinitions.eq_refl x6 Heq).
  - (* from_to: Prop proof irrelevance *)
    intro Heq.
    destruct Heq.
    set (from_proof := (Corelib.Init.Logic.eq_trans (Corelib.Init.Logic.eq_sym _) (Corelib.Init.Logic.eq_trans _ _))).
    pose proof (Stdlib.Logic.ProofIrrelevance.proof_irrelevance 
      (x3 = x3) from_proof (@Corelib.Init.Logic.eq_refl x1 x3)) as UIP.
    subst from_proof.
    rewrite UIP.
    apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
