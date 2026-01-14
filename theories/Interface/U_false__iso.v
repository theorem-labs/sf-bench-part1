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

Parameter imported_False : SProp.
Parameter False_iso : Iso False imported_False.
Existing Instance False_iso.
#[export] Hint Extern 0 (IsoStatementProofFor False ?x) => unify x False_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween False imported_False ?x) => unify x False_iso; constructor : typeclass_instances.


End Interface.