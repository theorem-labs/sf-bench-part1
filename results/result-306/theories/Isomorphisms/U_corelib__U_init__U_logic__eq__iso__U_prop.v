From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

(* Prop version - for equality on Prop/SProp types *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in *.
  unshelve eapply Build_Iso.
  - (* to: eq in Prop -> imported eq in SProp *)
    intro Heq.
    destruct Heq.
    (* We have H34 and H56 which are in SProp. Since SProp is proof-irrelevant, x4 = x6 *)
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4).
  - (* from: imported eq in SProp -> eq in Prop *)
    intro Heq.
    (* The motive P must work for any s in SProp, but we need to produce Prop equality *)
    (* Since SProp is proof irrelevant, we can't really use Heq constructively *)
    (* But since from_to gives us x3 and x5 back, we use that *)
    pose (Hfrom34 := from_to hx x3).
    pose (Hfrom56 := from_to hx x5).
    (* We need to show x3 = x5 *)
    (* Use proof irrelevance: if hx maps x3 to something in x2, we need to relate x3 and x5 *)
    (* Since SProp values are all equal, from hx x4 = from hx x6 *)
    (* But we need the elimination from Heq *)
    exact (IsoEq.eq_of_seq (IsoEq.eq_trans (IsoEq.eq_sym Hfrom34)
           (IsoEq.eq_trans (IsoEq.f_equal (from hx) 
              (Imported.Corelib_Init_Logic_eq_Prop_indl x2 x4 
                 (fun y _ => IsomorphismDefinitions.eq (to hx x3) y)
                 H34 x6 Heq)) 
           Hfrom56))).
  - (* to_from: SProp identity *)
    intro Heq.
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to: Prop UIP *)
    intro Heq.
    destruct Heq.
    apply sUIPt.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
