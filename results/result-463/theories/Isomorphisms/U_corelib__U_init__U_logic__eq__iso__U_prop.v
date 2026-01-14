From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Imported.Corelib_Init_Logic_eq_Prop is for SProp arguments *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For SProp equality, both types are proof-irrelevant *)
(* x1 is a Prop viewed as Type, x2 is an SProp. Both are proof-irrelevant. *)
(* The key insight: since this is for Prop-sorted equality, x1 is a proposition, 
   so by proof irrelevance, any two x3, x5 : x1 are equal *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  (* Both (x3 = x5) : Prop and (imported_Corelib_Init_Logic_eq_Prop x4 x6) : SProp are proof-irrelevant *)
  unshelve eapply Build_Iso.
  - intro Heq.
    destruct H34. destruct H56. destruct Heq.
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
  - intro Hseq.
    destruct H34. destruct H56.
    (* We need x3 = x5 : x1. Since Corelib_Init_Logic_eq_Prop is in SProp, we use match. *)
    (* The eliminator for SProp inductive types into SInhabited works *)
    (* First we get x3 = from hx (to hx x5), then we use from_to x5 to get x3 = x5 *)
    pose (step1 := sinhabitant (match Hseq in (Imported.Corelib_Init_Logic_eq_Prop _ _ y) return SInhabited (x3 = from hx y) with
      | Imported.Corelib_Init_Logic_eq_Prop_refl _ _ => 
          sinhabits (match from_to hx x3 in (IsomorphismDefinitions.eq _ r) return (r = from hx (to hx x3)) with
                    | IsomorphismDefinitions.eq_refl => Logic.eq_refl 
                    end)
      end)).
    (* step1 : x3 = from hx (to hx x5) *)
    (* Now use from_to hx x5 to get from hx (to hx x5) = x5 *)
    exact (match from_to hx x5 in (IsomorphismDefinitions.eq _ r) return (x3 = r) with
           | IsomorphismDefinitions.eq_refl => step1
           end).
  - intro Hseq. apply IsomorphismDefinitions.eq_refl.
  - intro Heq. destruct H34. destruct H56. destruct Heq.
    apply seq_of_eq. apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
