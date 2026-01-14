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

Parameter imported_iff : SProp -> SProp -> SProp.
Parameter iff_iso : forall (x1 : Prop) (x2 : SProp), Iso x1 x2 -> forall (x3 : Prop) (x4 : SProp), Iso x3 x4 -> Iso (x1 <-> x3) (imported_iff x2 x4).
Existing Instance iff_iso.
#[export] Hint Extern 0 (IsoStatementProofFor iff ?x) => unify x iff_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween iff imported_iff ?x) => unify x iff_iso; constructor : typeclass_instances.


End Interface.