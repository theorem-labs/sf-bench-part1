From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Helper: transport along IsomorphismDefinitions.eq to construct Imported.Corelib_Init_Logic_eq_Prop *)
(* In SProp, all inhabitants are equal, so we just need reflexivity *)
Definition imported_eq_transport_Prop {A : SProp} (x y : A) 
  : Imported.Corelib_Init_Logic_eq_Prop A x y.
Proof.
  (* In SProp, x and y are definitionally equal *)
  exact (Imported.Eq_refl_inst1 A x).
Defined.

(* For Prop -> SProp isomorphisms, we need a different approach *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unshelve eapply Build_Iso.
  - (* to: eq in Prop -> eq in SProp *)
    intro Heq.
    destruct Heq.
    unfold imported_Corelib_Init_Logic_eq_Prop.
    apply imported_eq_transport_Prop.
  - (* from: eq in SProp -> eq in Prop *)
    intro Heq.
    pose proof (from_to hx x3) as Hx3.
    pose proof (from_to hx x5) as Hx5.
    apply IsoEq.eq_of_seq.
    apply (IsoEq.eq_trans (IsoEq.eq_sym Hx3)).
    apply (IsoEq.eq_trans (IsoEq.f_equal (from hx) H34)).
    (* In SProp, x4 = x6 since the imported eq is inhabited *)
    apply (IsoEq.eq_trans (IsoEq.f_equal (from hx) (IsoEq.eq_sym H56))).
    exact Hx5.
  - (* to_from *)
    intro Heq.
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro Heq.
    destruct Heq.
    apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
