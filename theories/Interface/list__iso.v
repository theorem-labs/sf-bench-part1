From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

Module Export CodeBlocks.

End CodeBlocks.

Module Type Args. End Args.

Module Type Interface (Import args : Args).

Parameter imported_list : Type -> Type.
Parameter list_iso : forall x1 x2 : Type, Iso x1 x2 -> Iso (list x1) (imported_list x2).
Existing Instance list_iso.
#[export] Hint Extern 0 (IsoStatementProofFor list ?x) => unify x list_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween list imported_list ?x) => unify x list_iso; constructor : typeclass_instances.


End Interface.