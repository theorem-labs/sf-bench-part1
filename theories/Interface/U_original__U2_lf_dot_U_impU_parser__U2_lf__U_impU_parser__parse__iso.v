From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__optionU_e__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso Interface.U_string__string__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__optionU_e__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso Interface.U_string__string__iso.

  Export Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__optionU_e__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso.CodeBlocks Interface.U_string__string__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__optionU_e__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso.Interface <+ Interface.U_string__string__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__ImpParser_LF_ImpParser_parse : imported_String_string -> imported_Original_LF__DOT__ImpParser_LF_ImpParser_optionE imported_Original_LF__DOT__Imp_LF_Imp_com.
Parameter Original_LF__DOT__ImpParser_LF_ImpParser_parse_iso : forall (x1 : String.string) (x2 : imported_String_string),
  rel_iso String_string_iso x1 x2 ->
  rel_iso (Original_LF__DOT__ImpParser_LF_ImpParser_optionE_iso Original_LF__DOT__Imp_LF_Imp_com_iso) (Original.LF_DOT_ImpParser.LF.ImpParser.parse x1)
    (imported_Original_LF__DOT__ImpParser_LF_ImpParser_parse x2).
Existing Instance Original_LF__DOT__ImpParser_LF_ImpParser_parse_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_ImpParser.LF.ImpParser.parse ?x) => unify x Original_LF__DOT__ImpParser_LF_ImpParser_parse_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_ImpParser.LF.ImpParser.parse imported_Original_LF__DOT__ImpParser_LF_ImpParser_parse ?x) => unify x Original_LF__DOT__ImpParser_LF_ImpParser_parse_iso; constructor : typeclass_instances.


End Interface.