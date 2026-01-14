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

Parameter imported_false : imported_bool.
Parameter false_iso : rel_iso bool_iso false imported_false.
Existing Instance false_iso.
#[export] Hint Extern 0 (IsoStatementProofFor false ?x) => unify x false_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween false imported_false ?x) => unify x false_iso; constructor : typeclass_instances.


End Interface.