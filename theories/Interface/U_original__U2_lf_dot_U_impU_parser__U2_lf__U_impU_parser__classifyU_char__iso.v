From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__chartype__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__chartype__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__chartype__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__chartype__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__ImpParser_LF_ImpParser_classifyChar : imported_Ascii_ascii -> imported_Original_LF__DOT__ImpParser_LF_ImpParser_chartype.
Parameter Original_LF__DOT__ImpParser_LF_ImpParser_classifyChar_iso : forall (x1 : Ascii.ascii) (x2 : imported_Ascii_ascii),
  rel_iso Ascii_ascii_iso x1 x2 ->
  rel_iso Original_LF__DOT__ImpParser_LF_ImpParser_chartype_iso (Original.LF_DOT_ImpParser.LF.ImpParser.classifyChar x1) (imported_Original_LF__DOT__ImpParser_LF_ImpParser_classifyChar x2).
Existing Instance Original_LF__DOT__ImpParser_LF_ImpParser_classifyChar_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_ImpParser.LF.ImpParser.classifyChar ?x) => unify x Original_LF__DOT__ImpParser_LF_ImpParser_classifyChar_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_ImpParser.LF.ImpParser.classifyChar imported_Original_LF__DOT__ImpParser_LF_ImpParser_classifyChar ?x) => unify x Original_LF__DOT__ImpParser_LF_ImpParser_classifyChar_iso; constructor : typeclass_instances.


End Interface.