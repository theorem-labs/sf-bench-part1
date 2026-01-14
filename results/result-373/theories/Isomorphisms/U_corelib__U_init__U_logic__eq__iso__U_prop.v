From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Helper lemma: isomorphisms are injective *)
Lemma iso_injective_prop : forall (A : Type) (B : SProp) (i : Iso A B) (x y : A),
  IsomorphismDefinitions.eq (to i x) (to i y) -> x = y.
Proof.
  intros A B i x y Heq.
  pose proof (from_to i x) as Hft_x.
  pose proof (from_to i y) as Hft_y.
  destruct Hft_x. destruct Hft_y.
  reflexivity.
Qed.

(* For SProp equality at Prop level, we construct a direct isomorphism. *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  assert (Heq35 : x3 = x5).
  { pose proof (from_to hx x3) as Hft3.
    pose proof (from_to hx x5) as Hft5.
    destruct Hft3. destruct Hft5.
    reflexivity. }
  unshelve eapply Build_Iso.
  - (* to: (x3 = x5) -> imported_Corelib_Init_Logic_eq_Prop x4 x6 *)
    intros Heq_. destruct H34. destruct H56.
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl x2 (to hx x3)).
  - (* from: imported_Corelib_Init_Logic_eq_Prop x4 x6 -> (x3 = x5) *)
    intros Hseq_. exact Heq35.
  - (* to_from *)
    intro Hseq. apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro Heq.
    apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
