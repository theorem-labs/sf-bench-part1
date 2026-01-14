From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Eq for Prop types - SProp equality on SProp elements *)
(* For SProp inhabitants, all elements are equal, so we return True *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := 
  Imported.Corelib_Init_Logic_eq_Prop.

Instance Corelib_Init_Logic_eq_iso_Prop : 
  forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), 
    rel_iso hx x3 x4 -> 
    forall (x5 : x1) (x6 : x2), 
      rel_iso hx x5 x6 -> 
      Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold imported_Corelib_Init_Logic_eq_Prop.
  unshelve eapply Build_Iso.
  - (* to: eq in Prop -> Imported.True (SProp) *)
    intro Heq. exact Imported.True_intro.
  - (* from: Imported.True -> eq in Prop *)
    intro Htrue.
    unfold rel_iso in *.
    (* x4 and x6 are in SProp x2, so they are definitionally equal *)
    (* from_to hx x3 : eq (from hx (hx x3)) x3 *)
    (* from_to hx x5 : eq (from hx (hx x5)) x5 *)
    (* Since x4 and x6 are in SProp, from hx x4 = from hx x6 *)
    (* We need to show x3 = x5 *)
    (* x3 = from(to x3) = from x4 = from x6 = from(to x5) = x5 *)
    pose (step1 := from_to hx x3). (* eq (from hx (hx x3)) x3 *)
    pose (step2 := from_to hx x5). (* eq (from hx (hx x5)) x5 *)
    (* Since x2 is SProp, from hx x4 and from hx x6 should be definitionally equal *)
    (* Actually x4 and x6 are both in SProp x2, so from hx x4 = from hx x6 in SProp sense *)
    (* We can use H34 and H56 to relate things *)
    (* H34 : to hx x3 = x4 (in SProp), H56 : to hx x5 = x6 (in SProp) *)
    (* Since all elements of SProp are equal, we need to be more careful *)
    (* from(to x3) = x3, from(to x5) = x5 *)
    (* to x3 and to x5 are in x2 which is SProp, so from(to x3) = from(to x5) *)
    (* Thus x3 = from(to x3) = from(to x5) = x5 *)
    exact (IsoEq.eq_of_seq (IsoEq.eq_trans (IsoEq.eq_sym step1) step2)).
  - (* to_from: both are SProp, they're definitionally equal *)
    intro Heq.
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to: use UIP for Prop equality *)
    intro Heq.
    destruct Heq.
    apply sUIPt.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
