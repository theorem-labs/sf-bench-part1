From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.

Definition imported_and : SProp -> SProp -> SProp := Imported.and.

#[local] Unset Universe Polymorphism.
Instance and_iso : (forall (x1 : Prop) (x2 : SProp) (_ : Iso x1 x2) (x3 : Prop) (x4 : SProp) (_ : Iso x3 x4), Iso (and x1 x3) (imported_and x2 x4)).
Proof.
  intros x1 x2 H12 x3 x4 H34.
  unshelve eapply Build_Iso.
  - intro Ha. destruct Ha as [Ha1 Ha3].
    exact (@Imported.and_intro x2 x4 (to H12 Ha1) (to H34 Ha3)).
  - intro Hi. destruct Hi as [Hi2 Hi4].
    exact (conj (from H12 Hi2) (from H34 Hi4)).
  - intro Hi. destruct Hi as [Hi2 Hi4].
    apply IsomorphismDefinitions.eq_refl.
  - intro Ha. destruct Ha as [Ha1 Ha3].
    apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant and := {}.
Instance: KnownConstant Imported.and := {}.
Instance: IsoStatementProofFor and and_iso := {}.
Instance: IsoStatementProofBetween and Imported.and and_iso := {}.
