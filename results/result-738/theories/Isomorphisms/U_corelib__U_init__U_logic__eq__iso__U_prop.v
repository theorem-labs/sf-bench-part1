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

(* We define the isomorphism for Prop arguments *)
(* The interface expects: x1 : Type, x2 : SProp, with Iso x1 x2 *)
(* And x3, x5 : x1 with x4, x6 : x2 being related *)

(* Helper to convert seq equality to Logic equality *)
Lemma seq_to_eq_helper : forall {A : Type} {x y : A}, IsomorphismDefinitions.eq x y -> x = y.
Proof.
  intros A x y H. destruct H. reflexivity.
Qed.

Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  unshelve eapply Build_Iso.
  + (* to: x3 = x5 -> imported_Corelib_Init_Logic_eq_Prop x4 x6 *)
    intro Heq.
    destruct H34. destruct H56. destruct Heq.
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
  + (* from: imported_Corelib_Init_Logic_eq_Prop x4 x6 -> x3 = x5 *)
    intro Hseq.
    (* Since x2 is SProp, x4 and x6 are proof-irrelevant *)
    (* We have H34 : to hx x3 = x4 and H56 : to hx x5 = x6 (in SProp) *)
    (* All elements of x2 (SProp) are equal, so to hx x3 = to hx x5 in SProp *)
    (* This means from hx (to hx x3) = from hx (to hx x5) *)
    (* By from_to, x3 = x5 *)
    pose proof (from_to hx x3) as H3.
    pose proof (from_to hx x5) as H5.
    apply seq_to_eq_helper in H3.
    apply seq_to_eq_helper in H5.
    rewrite <- H3, <- H5.
    (* Now we need: from hx (to hx x3) = from hx (to hx x5) *)
    (* Since x2 is SProp, all its elements are equal *)
    (* to hx x3 : x2 and to hx x5 : x2, so they're equal in SProp *)
    reflexivity.
  + (* to_from *)
    intro s. reflexivity.
  + (* from_to *)
    intro Heq.
    destruct H34. destruct H56. destruct Heq.
    simpl.
    apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
