From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* This is an isomorphism between Prop eq on Type and SProp eq on SProp *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  destruct H34. destruct H56.
  (* Goal: Iso (x3 = x5) (Imported.Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5)) *)
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 -> Imported.Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) *)
    intro Heq. subst x5. apply Imported.Corelib_Init_Logic_eq_Prop_refl.
  - (* from: Imported.Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5) -> x3 = x5 *)
    intro Heq.
    (* Since x2 is SProp, (to hx x3) = (to hx x5) definitionally *)
    (* And by the isomorphism: x3 = from hx (to hx x3) = from hx (to hx x5) = x5 *)
    assert (H3 : from hx (to hx x3) = x3).
    { apply eq_of_seq. apply from_to. }
    assert (H5 : from hx (to hx x5) = x5).
    { apply eq_of_seq. apply from_to. }
    rewrite <- H3, <- H5.
    reflexivity.
  - (* to_from: SProp equality is trivial *)
    intro Heq. exact (IsomorphismDefinitions.eq_refl _).
  - (* from_to: need to show the round-trip is identity in SProp sense *)
    intro Heq. 
    (* Both Heq and the round-trip result are proofs of x3 = x5, use PI *)
    apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.PI.proof_irrelevance.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
