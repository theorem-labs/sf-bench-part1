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

Parameter imported_String_string : Type.
Parameter String_string_iso : Iso String.string imported_String_string.
Existing Instance String_string_iso.
#[export] Hint Extern 0 (IsoStatementProofFor String.string ?x) => unify x String_string_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween String.string imported_String_string ?x) => unify x String_string_iso; constructor : typeclass_instances.


End Interface.