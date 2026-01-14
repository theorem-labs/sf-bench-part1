From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Imported.Corelib_Init_Logic_eq_Prop is for SProp arguments *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Helper lemma: extract equality from SProp equality using the recl eliminator *)
Lemma from_eq_Prop_to_eq : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 x5 : x1),
  imported_Corelib_Init_Logic_eq_Prop (hx x3) (hx x5) -> x3 = x5.
Proof.
  intros x1 x2 hx x3 x5 Hseq.
  pose (P := fun (y : x2) (_ : Imported.Corelib_Init_Logic_eq_Prop x2 (hx x3) y) =>
    from hx (hx x3) = from hx y).
  assert (HP : P (hx x3) (Imported.Corelib_Init_Logic_eq_Prop_refl x2 (hx x3))).
  { unfold P. reflexivity. }
  pose proof (Imported.Corelib_Init_Logic_eq_Prop_recl x2 (hx x3) P HP (hx x5) Hseq) as H.
  unfold P in H.
  rewrite (from_to hx x3) in H.
  rewrite (from_to hx x5) in H.
  exact H.
Defined.

Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  destruct H34, H56.
  (* Now goal is: Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop (hx x3) (hx x5)) *)
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 -> imported_Corelib_Init_Logic_eq_Prop (hx x3) (hx x5) *)
    intro Heq. destruct Heq.
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
  - (* from: imported_Corelib_Init_Logic_eq_Prop (hx x3) (hx x5) -> x3 = x5 *)
    intro Hseq.
    exact (@from_eq_Prop_to_eq x1 x2 hx x3 x5 Hseq).
  - (* to_from *)
    intro Hseq.
    (* Both sides are in SProp, so they're equal by reflexivity *)
    reflexivity.
  - (* from_to *)
    intro Heq. destruct Heq.
    (* from (to eq_refl) = eq_refl *)
    (* to eq_refl = Corelib_Init_Logic_eq_Prop_refl *)
    (* from (refl) = from_eq_Prop_to_eq hx x3 x3 (refl) *)
    (* This should be eq_refl by computation, but the proof is not definitionally equal *)
    (* Use proof irrelevance since both are proofs of x3 = x3 in Prop *)
    apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
