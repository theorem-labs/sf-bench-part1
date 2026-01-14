From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Imported.Corelib_Init_Logic_eq_Prop is in SProp *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

From Stdlib Require Import Logic.ProofIrrelevance.

(* Helper: isomorphisms are injective *)
Lemma iso_injective_prop : forall (A : Type) (B : SProp) (i : Iso A B) (x y : A),
  IsomorphismDefinitions.eq (to i x) (to i y) -> x = y.
Proof.
  intros A B i x y H.
  rewrite <- (from_to i x).
  rewrite <- (from_to i y).
  destruct H.
  reflexivity.
Qed.

(* For Prop types, both x = y and the imported eq are in SProp, 
   so the isomorphism is essentially trivial due to SProp proof irrelevance *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  unshelve eapply Build_Iso.
  + intro Heq. destruct H34. destruct H56. destruct Heq.
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
  + intro Hseq. destruct H34. destruct H56.
    (* In SProp, we can use the fact that x4 = x6 (which is hx x3 = hx x5) *)
    (* We need to show x3 = x5 given hx x3 = hx x5 in SProp *)
    apply (iso_injective_prop hx x3 x5).
    (* Both sides are in SProp, so this is trivially true by proof irrelevance *)
    apply IsomorphismDefinitions.eq_refl.
  + intro Hseq. apply IsomorphismDefinitions.eq_refl.
  + intro Heq. destruct H34. destruct H56. destruct Heq.
    (* Use proof irrelevance for Prop equality *)
    rewrite (proof_irrelevance _ (iso_injective_prop hx x3 x3 eq_refl) Logic.eq_refl).
    apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
