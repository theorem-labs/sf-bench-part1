From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.nat__iso.

Module Export CodeBlocks.

  Export (hints) Interface.nat__iso.

  Export Interface.nat__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.nat__iso.Args <+ Interface.nat__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_0 : imported_nat.
Parameter _0_iso : rel_iso nat_iso 0 imported_0.
Existing Instance _0_iso.
#[export] Hint Extern 0 (IsoStatementProofFor 0 ?x) => unify x _0_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween 0 imported_0 ?x) => unify x _0_iso; constructor : typeclass_instances.


End Interface.