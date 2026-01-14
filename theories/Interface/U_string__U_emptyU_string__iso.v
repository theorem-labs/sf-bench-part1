From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_string__string__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_string__string__iso.

  Export Interface.U_string__string__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_string__string__iso.Args <+ Interface.U_string__string__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_String_EmptyString : imported_String_string.
Parameter String_EmptyString_iso : rel_iso String_string_iso String.EmptyString imported_String_EmptyString.
Existing Instance String_EmptyString_iso.
#[export] Hint Extern 0 (IsoStatementProofFor String.EmptyString ?x) => unify x String_EmptyString_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween String.EmptyString imported_String_EmptyString ?x) => unify x String_EmptyString_iso; constructor : typeclass_instances.


End Interface.