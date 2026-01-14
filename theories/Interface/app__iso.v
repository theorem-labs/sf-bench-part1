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

Parameter imported_app : forall x : Type, imported_list x -> imported_list x -> imported_list x.
Parameter app_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : list x1) (x4 : imported_list x2),
  rel_iso (list_iso hx) x3 x4 -> forall (x5 : list x1) (x6 : imported_list x2), rel_iso (list_iso hx) x5 x6 -> rel_iso (list_iso hx) (x3 ++ x5)%list (imported_app x4 x6).
Existing Instance app_iso.
#[export] Hint Extern 0 (IsoStatementProofFor app ?x) => unify x app_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween app imported_app ?x) => unify x app_iso; constructor : typeclass_instances.


End Interface.