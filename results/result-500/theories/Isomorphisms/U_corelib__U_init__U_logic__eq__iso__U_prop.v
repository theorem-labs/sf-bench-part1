From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* The Imported.Corelib_Init_Logic_eq_Prop takes SProp as its type parameter
   and compares elements of that SProp *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Isomorphism between Corelib.Init.Logic.eq (on Prop which maps to SProp) 
   and Imported.Corelib_Init_Logic_eq_Prop *)
(* This is for when we have Prop types x1 that map to SProp types x2 *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), 
  rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unshelve eapply Build_Iso.
  - (* to: eq in Prop -> eq in SProp *)
    intro Heq.
    destruct Heq.
    unfold imported_Corelib_Init_Logic_eq_Prop.
    (* Now x3 = x5, so H34 and H56 both relate x3 to elements of x2 (SProp) *)
    (* We need Imported.Corelib_Init_Logic_eq_Prop x2 x4 x6 *)
    (* H34 : IsomorphismDefinitions.eq (to hx x3) x4 *)
    (* H56 : IsomorphismDefinitions.eq (to hx x3) x6 *)
    (* So we can derive eq x4 x6 *)
    pose proof (IsoEq.eq_trans (IsoEq.eq_sym H34) H56) as Hx4x6.
    (* Now Hx4x6 : IsomorphismDefinitions.eq x4 x6 *)
    (* Transport along this to get Imported.Corelib_Init_Logic_eq_Prop x2 x4 x6 *)
    exact (IsoEq.eq_srect (fun w => Imported.Corelib_Init_Logic_eq_Prop x2 x4 w) 
             (Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4) Hx4x6).
  - (* from: eq in SProp -> eq in Prop *)
    intro Heq.
    pose proof (from_to hx x3) as Hx3.
    pose proof (from_to hx x5) as Hx5.
    pose proof (IsoEq.f_equal (from hx) H34) as Hf34.
    pose proof (IsoEq.f_equal (from hx) H56) as Hf56.
    (* Get x4 = x6 from Heq *)
    pose proof (Imported.Corelib_Init_Logic_eq_Prop_indl x2 x4 
                  (fun z _ => IsomorphismDefinitions.eq x4 z) 
                  IsomorphismDefinitions.eq_refl x6 Heq) as HfeqHeq.
    pose proof (IsoEq.f_equal (from hx) HfeqHeq) as HfromHeq.
    apply IsoEq.eq_of_seq.
    apply (IsoEq.eq_trans (IsoEq.eq_sym Hx3)).
    apply (IsoEq.eq_trans Hf34).
    apply (IsoEq.eq_trans HfromHeq).
    apply (IsoEq.eq_trans (IsoEq.eq_sym Hf56)).
    exact Hx5.
  - (* to_from *)
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
