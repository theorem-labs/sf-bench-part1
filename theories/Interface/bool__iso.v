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

Parameter imported_bool : Type.
Parameter bool_iso : Iso bool imported_bool.
Existing Instance bool_iso.
#[export] Hint Extern 0 (IsoStatementProofFor bool ?x) => unify x bool_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween bool imported_bool ?x) => unify x bool_iso; constructor : typeclass_instances.


End Interface.