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

Parameter imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist' : Type.
Parameter Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist'_iso : Iso Original.LF_DOT_IndPrinciples.LF.IndPrinciples.natlist' imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist'.
Existing Instance Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist'_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndPrinciples.LF.IndPrinciples.natlist' ?x) => unify x Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist'_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndPrinciples.LF.IndPrinciples.natlist' imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist' ?x) => unify x Original_LF__DOT__IndPrinciples_LF_IndPrinciples_natlist'_iso; constructor : typeclass_instances.


End Interface.