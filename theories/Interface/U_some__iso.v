From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.option__iso.

Module Export CodeBlocks.

  Export (hints) Interface.option__iso.

  Export Interface.option__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.option__iso.Args <+ Interface.option__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Some : forall x : Type, x -> imported_option x.
Parameter Some_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> rel_iso (option_iso hx) (Some x3) (imported_Some x4).
Existing Instance Some_iso.
#[export] Hint Extern 0 (IsoStatementProofFor (@Some) ?x) => unify x Some_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween (@Some) imported_Some ?x) => unify x Some_iso; constructor : typeclass_instances.


End Interface.