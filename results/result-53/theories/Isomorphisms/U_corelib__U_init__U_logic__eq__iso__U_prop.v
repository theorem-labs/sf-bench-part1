From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* The Imported.Corelib_Init_Logic_eq_Prop is in SProp *)
(* Must match the constraint exactly: (@Imported.Corelib_Init_Logic_eq_Prop) *)
Definition imported_Corelib_Init_Logic_eq_Prop := @Imported.Corelib_Init_Logic_eq_Prop.

(* For Prop-indexed equality, we need an isomorphism between:
   - Corelib.Init.Logic.eq (in Prop) on elements of a Type that's isomorphic to an SProp 
   - imported_Corelib_Init_Logic_eq_Prop (in SProp) on elements of the SProp
   
   Since both sides involve SProp-like things, we can use proof irrelevance. *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), 
  rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> 
  Iso (@Corelib.Init.Logic.eq x1 x3 x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unshelve eapply Build_Iso.
  - (* to: eq in Prop -> eq in SProp *)
    intro Heq.
    destruct Heq.
    (* x3 = x5, and H34 : eq (to hx x3) x4, H56 : eq (to hx x5) x6 = eq (to hx x3) x6 *)
    unfold imported_Corelib_Init_Logic_eq_Prop.
    (* Need: Imported.Corelib_Init_Logic_eq_Prop x4 x6 *)
    (* We have H34: eq (to hx x3) x4 and H56: eq (to hx x3) x6 *)
    pose proof (IsoEq.eq_trans (IsoEq.eq_sym H34) H56) as Heq46.
    exact (IsoEq.eq_srect (fun z => Imported.Corelib_Init_Logic_eq_Prop x2 x4 z) 
           (Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4) Heq46).
  - (* from: eq in SProp -> eq in Prop *)
    intro Heq.
    (* H34 : IsomorphismDefinitions.eq (to hx x3) x4 *)
    (* H56 : IsomorphismDefinitions.eq (to hx x5) x6 *)
    (* Heq : Imported.Corelib_Init_Logic_eq_Prop x4 x6 *)
    (* Need: x3 = x5 (in Prop) *)
    unfold imported_Corelib_Init_Logic_eq_Prop in Heq.
    pose proof (from_to hx x3) as Hx3.  (* eq (from hx (to hx x3)) x3 *)
    pose proof (from_to hx x5) as Hx5.  (* eq (from hx (to hx x5)) x5 *)
    pose proof (IsoEq.f_equal (from hx) H34) as Hf34. (* eq (from hx (to hx x3)) (from hx x4) *)
    pose proof (IsoEq.f_equal (from hx) H56) as Hf56. (* eq (from hx (to hx x5)) (from hx x6) *)
    (* Convert Heq to IsomorphismDefinitions.eq *)
    pose proof (Imported.Corelib_Init_Logic_eq_Prop_indl x2 x4 
                  (fun z _ => IsomorphismDefinitions.eq x4 z) 
                  IsomorphismDefinitions.eq_refl x6 Heq) as HfeqHeq. (* eq x4 x6 *)
    pose proof (IsoEq.f_equal (from hx) HfeqHeq) as HfromHeq. (* eq (from hx x4) (from hx x6) *)
    (* x3 = from hx (to hx x3) = from hx x4 = from hx x6 = from hx (to hx x5) = x5 *)
    apply IsoEq.eq_of_seq.
    apply (IsoEq.eq_trans (IsoEq.eq_sym Hx3)).
    apply (IsoEq.eq_trans Hf34).
    apply (IsoEq.eq_trans HfromHeq).
    apply (IsoEq.eq_trans (IsoEq.eq_sym Hf56)).
    exact Hx5.
  - (* to_from: SProp proof irrelevance *)
    intro Heq.
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro Heq.
    destruct Heq.
    apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
