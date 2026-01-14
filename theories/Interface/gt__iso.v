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

Parameter imported_gt : imported_nat -> imported_nat -> SProp.
Parameter gt_iso : forall (x1 : nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> forall (x3 : nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> Iso (x1 > x3) (imported_gt x2 x4).
Existing Instance gt_iso.
#[export] Hint Extern 0 (IsoStatementProofFor gt ?x) => unify x gt_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween gt imported_gt ?x) => unify x gt_iso; constructor : typeclass_instances.


End Interface.