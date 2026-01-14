From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__chartype__iso Interface.list__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__chartype__iso Interface.list__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__chartype__iso.CodeBlocks Interface.list__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__chartype__iso.Interface <+ Interface.list__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__helper : imported_Original_LF__DOT__ImpParser_LF_ImpParser_chartype -> imported_list imported_Ascii_ascii -> imported_list imported_Ascii_ascii -> imported_list (imported_list imported_Ascii_ascii).
Parameter Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__helper_iso : forall (x1 : Original.LF_DOT_ImpParser.LF.ImpParser.chartype) (x2 : imported_Original_LF__DOT__ImpParser_LF_ImpParser_chartype),
  rel_iso Original_LF__DOT__ImpParser_LF_ImpParser_chartype_iso x1 x2 ->
  forall (x3 : list Ascii.ascii) (x4 : imported_list imported_Ascii_ascii),
  rel_iso (list_iso Ascii_ascii_iso) x3 x4 ->
  forall (x5 : list Ascii.ascii) (x6 : imported_list imported_Ascii_ascii),
  rel_iso (list_iso Ascii_ascii_iso) x5 x6 ->
  rel_iso (list_iso (list_iso Ascii_ascii_iso)) (Original.LF_DOT_ImpParser.LF.ImpParser.tokenize_helper x1 x3 x5) (imported_Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__helper x2 x4 x6).
Existing Instance Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__helper_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_ImpParser.LF.ImpParser.tokenize_helper ?x) => unify x Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__helper_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_ImpParser.LF.ImpParser.tokenize_helper imported_Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__helper ?x) => unify x Original_LF__DOT__ImpParser_LF_ImpParser_tokenize__helper_iso; constructor : typeclass_instances.


End Interface.