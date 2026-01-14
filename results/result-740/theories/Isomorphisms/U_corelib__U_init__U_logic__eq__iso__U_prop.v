From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* The Imported.Corelib_Init_Logic_eq_Prop is now in SProp (since we defined it as Prop in Lean) *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Since Corelib_Init_Logic_eq_Prop takes SProp arguments and returns SProp,
   we need to show iso between Prop eq and SProp eq *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  (* Both are proof irrelevant (Prop and SProp), so any inhabitants are isomorphic *)
  unshelve eapply Build_Iso.
  - (* to: eq in Prop -> eq_Prop in SProp *)
    intro Heq.
    destruct Heq.
    unfold imported_Corelib_Init_Logic_eq_Prop.
    (* After destruct, x5 becomes x3, H56 now has type rel_iso hx x3 x6 *)
    (* Need: Corelib_Init_Logic_eq_Prop x4 x6  
       We use H34 and H56 to show x4 = x6 in SProp *)
    (* H34 : eq (to hx x3) x4, H56 : eq (to hx x3) x6 *)
    (* So x4 = to hx x3 = x6 *)
    pose proof (IsoEq.eq_trans (IsoEq.eq_sym H34) H56) as Heq46.
    exact (@IsoEq.eq_srect x2 x4 (fun w => Imported.Corelib_Init_Logic_eq_Prop x2 x4 w) 
             (Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4) x6 Heq46).
  - (* from: eq_Prop in SProp -> eq in Prop *)
    intro Heq.
    pose proof (from_to hx x3) as Hx3.
    pose proof (from_to hx x5) as Hx5.
    pose proof (IsoEq.f_equal (from hx) H34) as Hf34.
    pose proof (IsoEq.f_equal (from hx) H56) as Hf56.
    (* Heq : Corelib_Init_Logic_eq_Prop x4 x6 in SProp 
       Need: x3 = x5 in Prop *)
    (* from hx x4 = from hx x6 by eq_srect on Heq *)
    pose proof (@Imported.Corelib_Init_Logic_eq_Prop_indl x2 x4 
             (fun z _ => IsomorphismDefinitions.eq (from hx x4) (from hx z)) 
             IsomorphismDefinitions.eq_refl x6 Heq) as Hfrom46.
    (* x3 = from hx (to hx x3) = from hx x4 (by Hf34) 
       x5 = from hx (to hx x5) = from hx x6 (by Hf56) 
       from hx x4 = from hx x6 (by Hfrom46) *)
    apply IsoEq.eq_of_seq.
    apply (IsoEq.eq_trans (IsoEq.eq_sym Hx3)).
    apply (IsoEq.eq_trans Hf34).
    apply (IsoEq.eq_trans Hfrom46).
    apply (IsoEq.eq_trans (IsoEq.eq_sym Hf56)).
    exact Hx5.
  - (* to_from *)
    intro Heq.
    (* SProp proof irrelevance - all proofs are equal *)
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro Heq.
    destruct Heq.
    apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
