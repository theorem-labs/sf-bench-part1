From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Version for Prop arguments *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Helper: isomorphisms are injective *)
Lemma iso_injective : forall (A B : Type) (i : Iso A B) (x y : A),
  to i x = to i y -> x = y.
Proof.
  intros A B i x y H.
  rewrite <- (from_to i x).
  rewrite <- (from_to i y).
  apply Logic.f_equal. exact H.
Qed.

Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  unfold imported_Corelib_Init_Logic_eq_Prop.
  (* Corelib_Init_Logic_eq_Prop is defined as MyTrue, which imports as Imported.True *)
  (* We need Iso (x3 = x5) Imported.MyTrue *)
  unshelve eapply Build_Iso.
  - intro Heq. exact Imported.MyTrue_intro.
  - intro Hprop. 
    destruct H34. destruct H56.
    (* We need x3 = x5 *)
    (* from_to says: from hx (to hx x3) = x3 *)
    rewrite <- (from_to hx x3).
    rewrite <- (from_to hx x5).
    reflexivity.
  - intro Hprop. apply IsomorphismDefinitions.eq_refl.
  - intro Heq. destruct H34. destruct H56. destruct Heq.
    (* from_to is SProp, and the goal is SProp equality, use proof irrelevance *)
    apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
