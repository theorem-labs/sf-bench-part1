From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.

Definition imported_or : SProp -> SProp -> SProp := Imported.or.

(* Helper: from SProp to SInhabited Prop *)
Definition or_from_sinhabited (x1 : Prop) (x2 : SProp) (H1 : Iso x1 x2)
                              (x3 : Prop) (x4 : SProp) (H2 : Iso x3 x4)
  : imported_or x2 x4 -> SInhabited (x1 \/ x3).
Proof.
  intro p. destruct p as [a | b].
  - exact (sinhabits (or_introl (from H1 a))).
  - exact (sinhabits (or_intror (from H2 b))).
Defined.

Monomorphic Instance or_iso : forall (x1 : Prop) (x2 : SProp), Iso x1 x2 -> forall (x3 : Prop) (x4 : SProp), Iso x3 x4 -> Iso (x1 \/ x3) (imported_or x2 x4).
Proof.
  intros x1 x2 H1 x3 x4 H2.
  unshelve eapply Build_Iso.
  - (* to: Prop -> SProp *)
    intro p. destruct p as [a | b].
    + exact (Imported.or_inl x2 x4 (to H1 a)).
    + exact (Imported.or_inr x2 x4 (to H2 b)).
  - (* from: SProp -> Prop using sinhabitant *)
    intro p. exact (sinhabitant (or_from_sinhabited H1 H2 p)).
  - (* to_from *)
    intro p. apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro p. destruct p as [a | b].
    + apply seq_of_eq. apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
    + apply seq_of_eq. apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant Corelib.Init.Logic.or := {}.
Instance: KnownConstant Imported.or := {}.
Instance: IsoStatementProofFor Corelib.Init.Logic.or or_iso := {}.
Instance: IsoStatementProofBetween Corelib.Init.Logic.or Imported.or or_iso := {}.
