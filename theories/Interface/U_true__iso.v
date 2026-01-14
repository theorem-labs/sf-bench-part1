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

Parameter imported_True : SProp.
Parameter True_iso : Iso True imported_True.
Existing Instance True_iso.
#[export] Hint Extern 0 (IsoStatementProofFor True ?x) => unify x True_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween True imported_True ?x) => unify x True_iso; constructor : typeclass_instances.


End Interface.