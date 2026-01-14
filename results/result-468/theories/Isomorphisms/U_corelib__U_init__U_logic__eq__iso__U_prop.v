From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Use proof irrelevance for equality proofs *)
Lemma eq_proofs_equal : forall (A : Type) (x y : A) (p q : x = y), p = q.
Proof.
  intros A x y p q.
  apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Qed.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For Prop/SProp case: x1 is Type, x2 is SProp *)
(* x3 = x5 is in Prop, imported_Corelib_Init_Logic_eq_Prop x4 x6 is in SProp *)
(* Since x2 is SProp, any two elements are equal by SProp's proof irrelevance *)

Definition eq_iso_to_Prop (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (H34 : IsomorphismDefinitions.eq (to hx x3) x4) (x5 : x1) (x6 : x2) (H56 : IsomorphismDefinitions.eq (to hx x5) x6)
  : x3 = x5 -> imported_Corelib_Init_Logic_eq_Prop x4 x6.
Proof.
  intro Heq.
  destruct H34. destruct H56. destruct Heq.
  exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
Defined.

Definition eq_iso_from_Prop (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (H34 : IsomorphismDefinitions.eq (to hx x3) x4) (x5 : x1) (x6 : x2) (H56 : IsomorphismDefinitions.eq (to hx x5) x6)
  : imported_Corelib_Init_Logic_eq_Prop x4 x6 -> x3 = x5.
Proof.
  intro Hseq.
  destruct H34. destruct H56.
  rewrite <- (from_to hx x3).
  rewrite <- (from_to hx x5).
  reflexivity.
Defined.

Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  unshelve eapply Build_Iso.
  + exact (@eq_iso_to_Prop x1 x2 hx x3 x4 H34 x5 x6 H56).
  + exact (@eq_iso_from_Prop x1 x2 hx x3 x4 H34 x5 x6 H56).
  + intro Hseq. reflexivity.
  + intro Heq.
    destruct H34. destruct H56. destruct Heq.
    unfold eq_iso_from_Prop, eq_iso_to_Prop. simpl.
    rewrite (@eq_proofs_equal x1 x3 x3 _ Logic.eq_refl).
    apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
