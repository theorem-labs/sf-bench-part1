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

Parameter imported_option : Type -> Type.
Parameter option_iso : forall x1 x2 : Type, Iso x1 x2 -> Iso (option x1) (imported_option x2).
Existing Instance option_iso.
#[export] Hint Extern 0 (IsoStatementProofFor option ?x) => unify x option_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween option imported_option ?x) => unify x option_iso; constructor : typeclass_instances.


End Interface.