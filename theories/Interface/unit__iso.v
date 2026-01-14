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

Parameter imported_unit : Type.
Parameter unit_iso : Iso unit imported_unit.
Existing Instance unit_iso.
#[export] Hint Extern 0 (IsoStatementProofFor unit ?x) => unify x unit_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween unit imported_unit ?x) => unify x unit_iso; constructor : typeclass_instances.


End Interface.