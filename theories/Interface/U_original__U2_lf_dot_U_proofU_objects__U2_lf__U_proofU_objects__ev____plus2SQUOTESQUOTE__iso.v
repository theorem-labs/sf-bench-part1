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

Parameter imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2'' : SProp.
Parameter Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2''_iso : Iso Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_plus2'' imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2''.
Existing Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2''_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_plus2'' ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2''_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_plus2'' imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2'' ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2''_iso; constructor : typeclass_instances.


End Interface.