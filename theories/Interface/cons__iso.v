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

Parameter imported_cons : forall x : Type, x -> imported_list x -> imported_list x.
Parameter cons_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2),
  rel_iso hx x3 x4 -> forall (x5 : list x1) (x6 : imported_list x2), rel_iso (list_iso hx) x5 x6 -> rel_iso (list_iso hx) (x3 :: x5)%list (imported_cons x4 x6).
Existing Instance cons_iso.
#[export] Hint Extern 0 (IsoStatementProofFor (@cons) ?x) => unify x cons_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween (@cons) imported_cons ?x) => unify x cons_iso; constructor : typeclass_instances.


End Interface.