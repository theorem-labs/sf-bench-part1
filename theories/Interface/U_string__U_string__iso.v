From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.U_string__string__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.U_string__string__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.U_string__string__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.U_string__string__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_String_String : imported_Ascii_ascii -> imported_String_string -> imported_String_string.
Parameter String_String_iso : forall (x1 : Ascii.ascii) (x2 : imported_Ascii_ascii),
  rel_iso Ascii_ascii_iso x1 x2 ->
  forall (x3 : String.string) (x4 : imported_String_string), rel_iso String_string_iso x3 x4 -> rel_iso String_string_iso (String.String x1 x3) (imported_String_String x2 x4).
Existing Instance String_String_iso.
#[export] Hint Extern 0 (IsoStatementProofFor String.String ?x) => unify x String_String_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween String.String imported_String_String ?x) => unify x String_String_iso; constructor : typeclass_instances.


End Interface.