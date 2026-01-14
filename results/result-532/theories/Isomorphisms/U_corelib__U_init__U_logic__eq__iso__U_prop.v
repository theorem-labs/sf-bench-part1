From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* The interface expects: forall x : SProp, x -> x -> SProp *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Helper lemma: isomorphisms are injective - version for Type -> SProp *)
Lemma iso_injective_SProp : forall (A : Type) (B : SProp) (i : Iso A B) (x y : A),
  IsomorphismDefinitions.eq (to i x) (to i y) -> x = y.
Proof.
  intros A B i x y H.
  (* Use from_to to convert back *)
  rewrite <- (eq_of_seq (from_to i x)).
  rewrite <- (eq_of_seq (from_to i y)).
  (* from (to x) = from (to y) if to x = to y in SProp *)
  destruct H.
  reflexivity.
Qed.

(* Helper to extract equality from SProp equality using sinhabitant *)
Definition from_sprop_eq {A : Type} {B : SProp} (i : Iso A B) (x y : A) 
  (H : Imported.Corelib_Init_Logic_eq_Prop B (to i x) (to i y)) : x = y.
Proof.
  (* We use sinhabitant to extract from SInhabited *)
  apply sinhabitant.
  destruct H.
  apply sinhabits.
  exact (@iso_injective_SProp A B i x y (IsomorphismDefinitions.eq_refl _)).
Defined.

(* The interface expects: forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) ... *)
(* This handles the case where original type is Prop (treated as Type) and imported is SProp *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  unshelve eapply Build_Iso.
  + intro Heq. destruct H34. destruct H56. destruct Heq.
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
  + intro Hseq.
    destruct H34. destruct H56.
    exact (from_sprop_eq hx x3 x5 Hseq).
  + intro Hseq.
    reflexivity.
  + intro Heq.
    apply IsoEq.seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
