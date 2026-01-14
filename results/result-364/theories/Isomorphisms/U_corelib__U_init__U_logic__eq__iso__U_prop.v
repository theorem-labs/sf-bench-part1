From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* The Prop version - standalone definitions *)
#[local] Unset Universe Polymorphism.
Definition imported_Corelib_Init_Logic_eq_Prop : forall (x : SProp), x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.
Global Arguments imported_Corelib_Init_Logic_eq_Prop x%_type_scope _ _.
#[local] Set Universe Polymorphism.

(* For SProp, we have proof irrelevance - all inhabitants are equal *)
(* The isomorphism between Corelib.Init.Logic.eq (when instantiated at Prop) and the imported version *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), 
  rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> 
  Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unshelve eapply Build_Iso.
  - (* to: eq in Prop -> eq_Prop in SProp *)
    intro Heq.
    destruct Heq.
    unfold imported_Corelib_Init_Logic_eq_Prop, Imported.Corelib_Init_Logic_eq_Prop.
    (* We need to show Imported.Corelib_Init_Logic_eq_inst1 x2 x4 x6 *)
    pose proof (Imported.Corelib_Init_Logic_eq_refl_inst1 x2 x4) as Hrefl.
    (* Need to transport from x4 x4 to x4 x6 *)
    pose proof (eq_trans (eq_sym H34) H56) as H46.
    exact (eq_srect (fun w => Imported.Corelib_Init_Logic_eq_inst1 x2 x4 w) Hrefl H46).
  - (* from: eq_Prop in SProp -> eq in Prop *)
    intro Heq.
    pose proof (from_to hx x3) as Hx3.
    pose proof (from_to hx x5) as Hx5.
    pose proof (IsoEq.f_equal (from hx) H34) as Hf34.
    pose proof (IsoEq.f_equal (from hx) H56) as Hf56.
    unfold imported_Corelib_Init_Logic_eq_Prop, Imported.Corelib_Init_Logic_eq_Prop in Heq.
    pose proof (Imported.Corelib_Init_Logic_eq_inst1_indl x2 x4 
      (fun z _ => IsomorphismDefinitions.eq x4 z) 
      IsomorphismDefinitions.eq_refl x6 Heq) as H46.
    pose proof (IsoEq.f_equal (from hx) H46) as HfromHeq.
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
