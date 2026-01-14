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

Parameter imported_None : forall x : Type, imported_option x.
Parameter None_iso : forall (x1 x2 : Type) (hx : Iso x1 x2), rel_iso (option_iso hx) None (imported_None x2).
Existing Instance None_iso.
#[export] Hint Extern 0 (IsoStatementProofFor (@None) ?x) => unify x None_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween (@None) imported_None ?x) => unify x None_iso; constructor : typeclass_instances.


End Interface.