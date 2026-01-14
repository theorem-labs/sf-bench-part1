From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Helper lemma: to direction *)
Lemma eq_iso_Prop_to_helper : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (H34 : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (H56 : @rel_iso x1 x2 hx x5 x6),
   @Corelib.Init.Logic.eq x1 x3 x5 -> @imported_Corelib_Init_Logic_eq_Prop x2 x4 x6.
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56 Heq.
  unfold rel_iso in *. simpl in *.
  subst x5.
  destruct H34 using eq_sind.
  destruct H56 using eq_sind.
  apply Imported.Corelib_Init_Logic_eq_Prop_refl.
Qed.

(* Helper lemma: from direction *)
Lemma eq_iso_Prop_from_helper : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (H34 : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (H56 : @rel_iso x1 x2 hx x5 x6),
   @imported_Corelib_Init_Logic_eq_Prop x2 x4 x6 -> @Corelib.Init.Logic.eq x1 x3 x5.
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56 Heq.
  unfold rel_iso in *. simpl in *.
  (* Use recl to eliminate imported eq into Type *)
  apply (Imported.Corelib_Init_Logic_eq_Prop_recl x2 x4 (fun y _ => from hx x4 = from hx y)) in Heq; [|reflexivity].
  refine (eq_rect (to hx x3) (fun y _ => from hx y = from hx x6 -> x3 = x5) _ x4 H34 Heq).
  refine (eq_rect (to hx x5) (fun y _ => from hx (to hx x3) = from hx y -> x3 = x5) _ x6 H56).
  intro H.
  rewrite !from_to in H.
  exact H.
Qed.

(* For SProp equality, the isomorphism is trivial because both types live in SProp *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unshelve eapply Build_Iso.
  - exact (@eq_iso_Prop_to_helper x1 x2 hx x3 x4 H34 x5 x6 H56).
  - exact (@eq_iso_Prop_from_helper x1 x2 hx x3 x4 H34 x5 x6 H56).
  - (* to_from: SProp proof irrelevance *) 
    intro x. apply IsomorphismDefinitions.eq_refl.
  - (* from_to: Prop, need to prove roundtrip *)
    intro x.
    (* Both sides are proofs of x3 = x5, use proof irrelevance for Prop *)
    pose proof (Stdlib.Logic.ProofIrrelevance.proof_irrelevance _ (@eq_iso_Prop_from_helper x1 x2 hx x3 x4 H34 x5 x6 H56 (@eq_iso_Prop_to_helper x1 x2 hx x3 x4 H34 x5 x6 H56 x)) x) as Hirr.
    rewrite Hirr.
    apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
