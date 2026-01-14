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

Parameter imported_Original_False : SProp.
Parameter Original_False_iso : Iso Original.False imported_Original_False.
Existing Instance Original_False_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.False ?x) => unify x Original_False_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.False imported_Original_False ?x) => unify x Original_False_iso; constructor : typeclass_instances.


End Interface.