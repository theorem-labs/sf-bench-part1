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

Parameter imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_better__t__tree__ind__type : SProp.
Parameter Original_LF__DOT__IndPrinciples_LF_IndPrinciples_better__t__tree__ind__type_iso : Iso Original.LF_DOT_IndPrinciples.LF.IndPrinciples.better_t_tree_ind_type imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_better__t__tree__ind__type.
Existing Instance Original_LF__DOT__IndPrinciples_LF_IndPrinciples_better__t__tree__ind__type_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndPrinciples.LF.IndPrinciples.better_t_tree_ind_type ?x) => unify x Original_LF__DOT__IndPrinciples_LF_IndPrinciples_better__t__tree__ind__type_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndPrinciples.LF.IndPrinciples.better_t_tree_ind_type imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_better__t__tree__ind__type ?x) => unify x Original_LF__DOT__IndPrinciples_LF_IndPrinciples_better__t__tree__ind__type_iso; constructor : typeclass_instances.


End Interface.