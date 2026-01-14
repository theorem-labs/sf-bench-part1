From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.bool__iso.

Module Export CodeBlocks.

  Export (hints) Interface.bool__iso.

  Export Interface.bool__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.bool__iso.Args <+ Interface.bool__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_true : imported_bool.
Parameter true_iso : rel_iso bool_iso true imported_true.
Existing Instance true_iso.
#[export] Hint Extern 0 (IsoStatementProofFor true ?x) => unify x true_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween true imported_true ?x) => unify x true_iso; constructor : typeclass_instances.


End Interface.