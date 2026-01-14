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

Parameter imported_Type : Type.
Parameter Type_iso : Iso Type imported_Type.
Existing Instance Type_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Type ?x) => unify x Type_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Type imported_Type ?x) => unify x Type_iso; constructor : typeclass_instances.


End Interface.