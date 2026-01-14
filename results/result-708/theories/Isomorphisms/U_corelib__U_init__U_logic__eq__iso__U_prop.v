From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Imported.Corelib_Init_Logic_eq_Prop is now in SProp (defined in Prop in Lean) *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Helper: from direction *)
Definition eq_iso_Prop_from' (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 x5 : x1)
  (Hseq : imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5)) : x3 = x5.
Proof.
  pose proof (from_to hx x3) as H3.
  pose proof (from_to hx x5) as H5.
  rewrite <- H3.
  rewrite <- H5.
  reflexivity.
Defined.

(* Helper: to direction *)
Definition eq_iso_Prop_to' (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 x5 : x1)
  (Heq : x3 = x5) : imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx x5).
Proof.
  destruct Heq. exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
Defined.

(* For equality types, proof irrelevance gives us what we need *)
Lemma eq_type_proof_irrelevance : forall (A : Type) (x y : A) (p q : x = y), p = q.
Proof. intros. apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance. Qed.

(* For Prop/SProp equality *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  destruct H34. destruct H56.
  unshelve eapply Build_Iso.
  - exact (@eq_iso_Prop_to' x1 x2 hx x3 x5).
  - exact (@eq_iso_Prop_from' x1 x2 hx x3 x5).
  - intro Hseq. reflexivity.
  - intro Heq.
    (* Use proof irrelevance: all equality proofs in Prop are equal *)
    apply seq_of_eq.
    apply eq_type_proof_irrelevance.
Qed.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
