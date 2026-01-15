From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

Module Export CodeBlocks.

End CodeBlocks.

Module Type Args. End Args.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_And_and : SProp -> SProp -> SProp.
Parameter Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_And_and_iso : (forall (x1 : Prop) (x2 : SProp) (_ : Iso x1 x2) (x3 : Prop) (x4 : SProp) (_ : Iso x3 x4),
   Iso (Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.And.and x1 x3) (imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_And_and x2 x4)).
Existing Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_And_and_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.And.and ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_And_and_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.And.and imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_And_and ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_And_and_iso; constructor : typeclass_instances.


End Interface.