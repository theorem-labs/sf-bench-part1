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

Parameter imported_Ascii_ascii : Type.
Parameter Ascii_ascii_iso : Iso Ascii.ascii imported_Ascii_ascii.
Existing Instance Ascii_ascii_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Ascii.ascii ?x) => unify x Ascii_ascii_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Ascii.ascii imported_Ascii_ascii ?x) => unify x Ascii_ascii_iso; constructor : typeclass_instances.


End Interface.