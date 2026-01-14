From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.list__iso.

Module Export CodeBlocks.

  Export (hints) Interface.list__iso.

  Export Interface.list__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.list__iso.Args <+ Interface.list__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_nil : forall x : Type, imported_list x.
Parameter nil_iso : forall (x1 x2 : Type) (hx : Iso x1 x2), rel_iso (list_iso hx) nil (imported_nil x2).
Existing Instance nil_iso.
#[export] Hint Extern 0 (IsoStatementProofFor (@nil) ?x) => unify x nil_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween (@nil) imported_nil ?x) => unify x nil_iso; constructor : typeclass_instances.


End Interface.