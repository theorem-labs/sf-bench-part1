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

Parameter imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree : Type -> Type.
Parameter Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree_iso : forall x1 x2 : Type, Iso x1 x2 -> Iso (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.tree x1) (imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree x2).
Existing Instance Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndPrinciples.LF.IndPrinciples.tree ?x) => unify x Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndPrinciples.LF.IndPrinciples.tree imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree ?x) => unify x Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree_iso; constructor : typeclass_instances.


End Interface.