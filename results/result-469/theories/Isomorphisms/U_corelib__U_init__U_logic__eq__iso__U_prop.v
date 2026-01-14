From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Imported.Corelib_Init_Logic_eq_Prop is in SProp (defined for Prop values in Lean) *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For Prop/SProp equality, build isomorphism.
   The key insight: Imported.Corelib_Init_Logic_eq_Prop is indexed by SProp values,
   but we have an Iso x1 x2, so from : x2 -> x1 maps back to Type.
   This allows us to recover Type-level equality. *)

From Stdlib Require Import Logic.ProofIrrelevance.

(* Helper: if to x = to y then x = y for an iso *)
Lemma iso_inj : forall (A : Type) (B : SProp) (i : Iso A B) (x y : A),
  from i (to i x) = x.
Proof.
  intros A B i x y.
  apply eq_of_seq. apply (from_to i).
Qed.

Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  unfold imported_Corelib_Init_Logic_eq_Prop.
  (* H34: eq (to hx x3) x4, H56: eq (to hx x5) x6 *)
  destruct H34. destruct H56.
  (* Now x4 = to hx x3, x6 = to hx x5 *)
  (* Goal: Iso (x3 = x5) (Imported.Corelib_Init_Logic_eq_Prop x2 (to hx x3) (to hx x5)) *)
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 -> Imported.Corelib_Init_Logic_eq_Prop x2 (to hx x3) (to hx x5) *)
    intro Heq. destruct Heq.
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
  - (* from: Imported.Corelib_Init_Logic_eq_Prop x2 (to hx x3) (to hx x5) -> x3 = x5 *)
    intro Hseq.
    pose proof (iso_inj hx x3 x3) as H3.
    pose proof (iso_inj hx x5 x5) as H5.
    rewrite <- H3. rewrite <- H5.
    destruct Hseq.
    exact Logic.eq_refl.
  - (* to_from *)
    intro Hseq. 
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to: need to show eq (from (to Heq)) Heq *)
    intro Heq.
    (* Both sides are equality proofs, use proof irrelevance *)
    apply seq_of_eq.
    apply proof_irrelevance.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
