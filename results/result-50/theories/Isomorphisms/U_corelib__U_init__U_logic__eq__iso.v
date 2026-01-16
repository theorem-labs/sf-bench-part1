From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
(* (* Typeclasses Opaque rel_iso. *) *)

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.
From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso__U_prop.

(* Use imported Corelib_Init_Logic_eq which is now in SProp *)
Definition imported_Corelib_Init_Logic_eq : forall x : Type, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq.

Instance Corelib_Init_Logic_eq_iso : (forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  destruct H34 as [H34']. destruct H56 as [H56'].
  simpl in H34', H56'.
  unshelve eapply Build_Iso.
  - (* to: eq in Prop -> eq in SProp *)
    intro Heq.
    subst x5.
    unfold imported_Corelib_Init_Logic_eq.
    (* H34' : to hx x3 = x4, H56' : to hx x3 = x6, goal: Imported.eq x4 x6 *)
    (* x4 and x6 should be equal via transitivity *)
    assert (x4x6 : x4 = x6).
    { apply eq_of_seq. eapply eq_trans. apply eq_sym. exact H34'. exact H56'. }
    subst x6.
    apply Imported.Corelib_Init_Logic_eq_refl.
  - (* from: eq in SProp -> eq in Prop *)
    intro Heq.
    unfold imported_Corelib_Init_Logic_eq in Heq.
    (* Heq : Imported.eq x4 x6, H34' : to hx x3 = x4, H56' : to hx x5 = x6 *)
    destruct Heq.
    (* Now x4 = x6, so from hx x4 = from hx x6 by injectivity *)
    (* We know from_to hx x3, from_to hx x5 *)
    assert (Hinj : x3 = x5).
    { transitivity (from hx (to hx x3)).
      - symmetry. apply eq_of_seq. apply (from_to hx).
      - transitivity (from hx (to hx x5)).
        + f_equal. apply eq_of_seq. eapply eq_trans. exact H34'. apply eq_sym. exact H56'.
        + apply eq_of_seq. apply (from_to hx).
    }
    exact Hinj.
  - (* to_from - SProp terms are definitionally equal *)
    intro Heq; apply IsomorphismDefinitions.eq_refl.
  - (* from_to - use Prop proof irrelevance *)
    intro Heq.
    apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq) Corelib_Init_Logic_eq_iso := {}.

(* Prop version - for equality specialized to Prop/SProp *)
(* This is exposed via the file Isomorphisms/U_corelib__U_init__U_logic__eq__iso__U_prop.v *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 -> imported_Corelib_Init_Logic_eq_Prop x4 x6 *)
    intro Heq.
    apply Imported.Corelib_Init_Logic_eq_Prop_refl.
  - (* from: imported_Corelib_Init_Logic_eq_Prop x4 x6 -> x3 = x5 *)
    intro Heq.
    transitivity (from hx (to hx x3)).
    + symmetry. apply eq_of_seq. apply (from_to hx).
    + transitivity (from hx (to hx x5)).
      * reflexivity.
      * apply eq_of_seq. apply (from_to hx).
  - intro x; apply IsomorphismDefinitions.eq_refl.
  - intro x; apply seq_of_eq. apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.
