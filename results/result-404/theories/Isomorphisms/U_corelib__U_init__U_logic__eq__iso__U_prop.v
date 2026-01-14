From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* This is an isomorphism between Prop eq (on Prop types) and SProp eq *)
(* For x1 : Type, x2 : SProp with Iso x1 x2, we need:
   Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6) 
   where x3, x5 : x1 and x4, x6 : x2, and imported_Corelib_Init_Logic_eq_Prop : SProp -> ... *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  destruct H34. destruct H56.
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 -> imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) *)
    intro Heq. subst x5. 
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl x2 (to hx x3)).
  - (* from: imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) -> x3 = x5 *)
    intro Heq.
    (* Use from_to which is in IsomorphismDefinitions.eq (SProp eq) *)
    pose proof (from_to hx x3) as Hft3.
    pose proof (from_to hx x5) as Hft5.
    (* Convert SProp eq to Prop eq using eq_of_seq *)
    pose proof (eq_of_seq Hft3) as Hft3'.
    pose proof (eq_of_seq Hft5) as Hft5'.
    (* Now Hft3' : from hx (to hx x3) = x3 and Hft5' : from hx (to hx x5) = x5 *)
    (* We need x3 = x5 *)
    (* Since x2 : SProp, to hx x3 and to hx x5 are definitionally equal *)
    (* So from hx (to hx x3) = from hx (to hx x5) *)
    transitivity (from hx (to hx x3)).
    + symmetry. exact Hft3'.
    + transitivity (from hx (to hx x5)).
      * reflexivity.
      * exact Hft5'.
  - (* to_from *)
    intro Heq. exact (IsomorphismDefinitions.eq_refl _).
  - (* from_to *)
    intro Heq.
    (* Use proof irrelevance *)
    apply seq_of_eq.
    apply (Stdlib.Logic.ProofIrrelevance.proof_irrelevance _ _ _).
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
