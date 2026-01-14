From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Key lemma: if x1 has Iso to SProp x2, then any two inhabitants of x1 are equal *)
Lemma iso_to_SProp_implies_proof_irrel (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) : 
  forall (a b : x1), a = b.
Proof.
  intros a b.
  pose proof (from_to hx a) as Ha.
  pose proof (from_to hx b) as Hb.
  rewrite <- Ha, <- Hb.
  reflexivity.
Qed.

(* This is an isomorphism between Prop eq (with Prop arguments) and SProp eq *)
Definition Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (H34 : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (H56 : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  destruct H34. destruct H56.
  unshelve eapply Build_Iso.
  - intro Heq. subst x5. apply Imported.Corelib_Init_Logic_eq_Prop_refl.
  - intros _.
    apply iso_to_SProp_implies_proof_irrel with (x2 := x2).
    exact hx.
  - intro Heq. exact (IsomorphismDefinitions.eq_refl _).
  - intro Heq.
    destruct Heq.
    (* Now goal is: eq (iso_to_SProp_implies_proof_irrel hx x3 x3) eq_refl *)
    (* Both are proofs of x3 = x3, and we need IsomorphismDefinitions.eq between them *)
    (* Use seq_of_peq_t which converts Prop equality to SProp eq@{Type} *)
    apply seq_of_peq_t.
    (* Now we need: (iso_to_SProp_implies_proof_irrel hx x3 x3) = Logic.eq_refl in Prop *)
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

#[export] Instance Corelib_Init_Logic_eq_iso_Prop_instance : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (H34 : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (H56 : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)) := Corelib_Init_Logic_eq_iso_Prop.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
