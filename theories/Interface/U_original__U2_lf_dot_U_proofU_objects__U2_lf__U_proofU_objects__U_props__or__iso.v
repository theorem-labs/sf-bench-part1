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

Parameter imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or : SProp -> SProp -> SProp.
Parameter Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or_iso : forall (x1 : Prop) (x2 : SProp),
  Iso x1 x2 -> forall (x3 : Prop) (x4 : SProp), Iso x3 x4 -> Iso (Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.or x1 x3) (imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or x2 x4).
Existing Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.or ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.or imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or_iso; constructor : typeclass_instances.


End Interface.