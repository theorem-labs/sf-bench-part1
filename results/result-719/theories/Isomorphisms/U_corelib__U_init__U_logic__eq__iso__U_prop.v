From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* For Props, we use the imported Prop version *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := 
  @Imported.Corelib_Init_Logic_eq_Prop.

(* Helper to convert Imported eq_Prop to IsomorphismDefinitions eq *)
Definition imported_eq_Prop_to_iso_eq {A : SProp} {x y : A} 
  (H : Imported.Corelib_Init_Logic_eq_Prop A x y) : IsomorphismDefinitions.eq x y :=
  Imported.Corelib_Init_Logic_eq_Prop_indl A x 
    (fun z _ => IsomorphismDefinitions.eq x z) 
    IsomorphismDefinitions.eq_refl y H.

Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), 
  rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unshelve eapply Build_Iso.
  - intro Heq. destruct Heq.
    unfold imported_Corelib_Init_Logic_eq_Prop.
    (* x4 and x6 are both in x2 : SProp, so they are equal by proof irrelevance *)
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4).
  - intro Heq.
    unfold imported_Corelib_Init_Logic_eq_Prop in Heq.
    pose proof (from_to hx x3) as Hx3.
    pose proof (from_to hx x5) as Hx5.
    pose proof (IsoEq.f_equal (from hx) H34) as Hf34.
    pose proof (IsoEq.f_equal (from hx) H56) as Hf56.
    pose proof (imported_eq_Prop_to_iso_eq Heq) as HfeqHeq.
    pose proof (IsoEq.f_equal (from hx) HfeqHeq) as HfromHeq.
    apply IsoEq.eq_of_seq.
    apply (IsoEq.eq_trans (IsoEq.eq_sym Hx3)).
    apply (IsoEq.eq_trans Hf34).
    apply (IsoEq.eq_trans HfromHeq).
    apply (IsoEq.eq_trans (IsoEq.eq_sym Hf56)).
    exact Hx5.
  - intro Heq. apply IsomorphismDefinitions.eq_refl.
  - intro Heq. destruct Heq. apply IsomorphismDefinitions.eq_refl.
Defined.
