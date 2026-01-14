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

(* For SProp types, both Prop equality and SProp equality are trivially related *)
(* Since x2 is SProp, any two elements are definitionally equal *)

(* Use proof irrelevance for the from_to direction *)
Lemma eq_proofs_equal_Prop : forall (A : Type) (x y : A) (p q : x = y), p = q.
Proof.
  intros A x y p q.
  apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Qed.

Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  unshelve eapply Build_Iso.
  + (* to : x3 = x5 -> imported_Corelib_Init_Logic_eq_Prop x4 x6 *)
    intro Heq.
    destruct H34. destruct H56. destruct Heq.
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
  + (* from : imported_Corelib_Init_Logic_eq_Prop x4 x6 -> x3 = x5 *)
    intro Hseq.
    destruct H34. destruct H56.
    (* Use the recursor for Corelib_Init_Logic_eq_Prop to get x3 = from hx (hx x5) *)
    (* Then compose with from_to to get x3 = x5 *)
    assert (Heq1 : x3 = from hx (hx x5)).
    { refine (Imported.Corelib_Init_Logic_eq_Prop_recl _ _ (fun y _ => x3 = from hx y) _ _ Hseq).
      (* Goal: x3 = from hx (to hx x3) *)
      exact (Logic.eq_sym (eq_of_seq (from_to hx x3))). }
    assert (Heq2 : from hx (hx x5) = x5).
    { exact (eq_of_seq (from_to hx x5)). }
    exact (Logic.eq_trans Heq1 Heq2).
  + (* to_from *)
    intro Hseq.
    reflexivity.
  + (* from_to *)
    intro Heq.
    destruct H34. destruct H56.
    (* Both sides are proofs of x3 = x5, use proof irrelevance *)
    destruct Heq.
    apply seq_of_eq.
    apply eq_proofs_equal_Prop.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
