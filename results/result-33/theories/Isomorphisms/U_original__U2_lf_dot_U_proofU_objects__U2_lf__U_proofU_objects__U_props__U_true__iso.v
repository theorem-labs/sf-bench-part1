From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
#[local] Set Printing Coercions.

Monomorphic Definition imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_True : SProp := Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_True.

Monomorphic Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_True_iso : Iso Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.True imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_True.
Proof.
  unshelve eapply Build_Iso.
  - (* to: Prop -> SProp *)
    intro p. exact Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_True_I.
  - (* from: SProp -> Prop *)
    intro p. destruct p. exact Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.I.
  - (* to_from *)
    intro p. apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro p. destruct p. apply seq_of_eq. apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.True := {}.
Instance: KnownConstant Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_True := {}.
Instance: IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.True Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_True_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.True Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_True Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_True_iso := {}.
