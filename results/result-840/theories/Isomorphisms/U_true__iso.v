From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.

Definition imported_True : SProp := Imported.True.

Instance True_iso : Iso True imported_True.
Proof.
  unshelve eapply Build_Iso.
  - intro H; exact Imported.True_intro.
  - intro H; exact Logic.I.
  - intro x; apply IsomorphismDefinitions.eq_refl.
  - intro x; apply seq_of_eq. 
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.
Instance: KnownConstant True := {}.
Instance: KnownConstant Imported.True := {}.
Instance: IsoStatementProofFor True True_iso := {}.
Instance: IsoStatementProofBetween True Imported.True True_iso := {}.
