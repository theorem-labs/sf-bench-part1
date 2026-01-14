From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.prod__iso.

Module Export CodeBlocks.

  Export (hints) Interface.prod__iso.

  Export Interface.prod__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.prod__iso.Args <+ Interface.prod__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_pair : forall x x0 : Type, x -> x0 -> imported_prod x x0.
Parameter pair_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 x4 : Type) (hx0 : Iso x3 x4) (x5 : x1) (x6 : x2),
  rel_iso hx x5 x6 -> forall (x7 : x3) (x8 : x4), rel_iso hx0 x7 x8 -> rel_iso (prod_iso hx hx0) (x5, x7) (imported_pair x6 x8).
Existing Instance pair_iso.
#[export] Hint Extern 0 (IsoStatementProofFor (@pair) ?x) => unify x pair_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween (@pair) imported_pair ?x) => unify x pair_iso; constructor : typeclass_instances.


End Interface.