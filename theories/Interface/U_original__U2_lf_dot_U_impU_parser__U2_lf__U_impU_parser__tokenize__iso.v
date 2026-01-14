From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_string__string__iso Interface.list__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_string__string__iso Interface.list__iso.

  Export Interface.U_string__string__iso.CodeBlocks Interface.list__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_string__string__iso.Interface <+ Interface.list__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__ImpParser_LF_ImpParser_tokenize : imported_String_string -> imported_list imported_String_string.
Parameter Original_LF__DOT__ImpParser_LF_ImpParser_tokenize_iso : forall (x1 : String.string) (x2 : imported_String_string),
  rel_iso String_string_iso x1 x2 -> rel_iso (list_iso String_string_iso) (Original.LF_DOT_ImpParser.LF.ImpParser.tokenize x1) (imported_Original_LF__DOT__ImpParser_LF_ImpParser_tokenize x2).
Existing Instance Original_LF__DOT__ImpParser_LF_ImpParser_tokenize_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_ImpParser.LF.ImpParser.tokenize ?x) => unify x Original_LF__DOT__ImpParser_LF_ImpParser_tokenize_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_ImpParser.LF.ImpParser.tokenize imported_Original_LF__DOT__ImpParser_LF_ImpParser_tokenize ?x) => unify x Original_LF__DOT__ImpParser_LF_ImpParser_tokenize_iso; constructor : typeclass_instances.


End Interface.