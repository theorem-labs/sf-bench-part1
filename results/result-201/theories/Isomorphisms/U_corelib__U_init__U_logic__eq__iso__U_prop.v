From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
From Stdlib Require Import Logic.ProofIrrelevance.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Imported.Corelib_Init_Logic_eq_Prop for SProp types *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Helper to convert IsomorphismDefinitions.eq to Logic.eq *)
Definition seq_to_eq {A : Type} {x y : A} (H : IsomorphismDefinitions.eq x y) : x = y :=
  match H with IsomorphismDefinitions.eq_refl => Logic.eq_refl end.

(* Helper for injectivity using from_to *)
Lemma iso_injective_SProp : forall (A : Type) (B : SProp) (i : Iso A B) (x y : A),
  x = y.
Proof.
  intros A B i x y.
  pose proof (seq_to_eq (from_to i x)) as Hx.
  pose proof (seq_to_eq (from_to i y)) as Hy.
  rewrite <- Hx, <- Hy.
  reflexivity.
Qed.

(* Helper to convert Logic.eq to IsomorphismDefinitions.eq for Type *)
Definition peq_to_seq {A : Type} {x y : A} (H : x = y) : IsomorphismDefinitions.eq x y :=
  match H with Logic.eq_refl => IsomorphismDefinitions.eq_refl end.

(* For SProp types, all inhabitants are definitionally equal *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in *.
  unshelve eapply Build_Iso.
  - intro Heq.
    destruct Heq. destruct H34. destruct H56.
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl _ _).
  - intro Hseq.
    destruct H34. destruct H56.
    exact (iso_injective_SProp hx x3 x5).
  - intro Hseq. destruct Hseq.
    apply IsomorphismDefinitions.eq_refl.
  - intro Heq. destruct H34. destruct H56. destruct Heq.
    (* Need IsomorphismDefinitions.eq (iso_injective_SProp hx x3 x3) eq_refl *)
    (* Use proof irrelevance: all proofs of x3 = x3 are equal *)
    apply peq_to_seq.
    apply proof_irrelevance.
Qed.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
