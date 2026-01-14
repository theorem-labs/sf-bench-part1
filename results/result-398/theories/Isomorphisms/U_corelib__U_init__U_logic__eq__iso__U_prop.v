From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From Stdlib Require Import ProofIrrelevance.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* This is an isomorphism between Prop eq (on a Prop type that maps to SProp) and SProp eq *)
(* The key insight: when x1 (Type/Prop) maps to x2 (SProp), equality on x1 is in Prop,
   and equality on x2 is in SProp. Both are essentially trivial when inhabited 
   because all SProp values are equal. *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (H34 : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (H56 : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  destruct H34. destruct H56.
  (* Now x4 = to hx x3 and x6 = to hx x5 *)
  (* Goal: Iso (x3 = x5) (Imported.Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5)) *)
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 -> Imported.Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) *)
    intro Heq.
    subst x5.
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl x2 (to hx x3)).
  - (* from: Imported.Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) -> x3 = x5 *)
    intro Heq.
    (* Key insight: x2 : SProp, so (to hx x3) and (to hx x5) are the same SProp value *)
    (* When we apply from to both, we get (from hx (to hx x3)) and (from hx (to hx x5)) *)
    (* These are both in x1 : Type, and by from_to they equal x3 and x5 respectively *)
    apply sinhabitant.
    (* First get SInhabited (from hx (to hx x3) = from hx (to hx x5)) *)
    pose proof (Imported.Corelib_Init_Logic_eq_Prop_indl x2 (to hx x3)
              (fun y _ => SInhabited (from hx (to hx x3) = from hx y)) 
              (sinhabits (Corelib.Init.Logic.eq_refl _))
              (to hx x5) Heq) as H.
    (* H : SInhabited (from hx (to hx x3) = from hx (to hx x5)) *)
    (* from_to gives: eq (from hx (to hx x3)) x3 and eq (from hx (to hx x5)) x5 *)
    pose proof (from_to hx x3) as Hft3.
    pose proof (from_to hx x5) as Hft5.
    (* Transport: first move from hx (to hx x5) to x5 *)
    pose proof (IsoEq.eq_srect (fun z => SInhabited (from hx (to hx x3) = z)) H Hft5) as H'.
    (* H' : SInhabited (from hx (to hx x3) = x5) *)
    (* Now move from hx (to hx x3) to x3 using eq_srect with symmetric equality *)
    pose proof (IsoEq.eq_sym Hft3) as Hft3'.
    (* Hft3' : eq x3 (from hx (to hx x3)) *)
    exact (IsoEq.eq_srect_r (fun z => SInhabited (z = x5)) H' Hft3').
  - (* to_from *)
    intro Heq. exact (IsomorphismDefinitions.eq_refl _).
  - (* from_to *)
    intro Heq.
    (* We need to show IsomorphismDefinitions.eq (from (to Heq)) Heq *)
    (* Both are proofs of x3 = x5 in Prop, so use proof_irrelevance to get Logic.eq *)
    (* Then convert to IsomorphismDefinitions.eq using seq_of_peq_t (for Type) *)
    apply IsoEq.seq_of_eq.
    apply proof_irrelevance.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
