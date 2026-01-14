From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__optionU_e__iso Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__token__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso Interface.list__iso Interface.nat__iso Interface.prod__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__optionU_e__iso Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__token__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso Interface.list__iso Interface.nat__iso Interface.prod__iso.

  Export Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__optionU_e__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__token__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso.CodeBlocks Interface.list__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.prod__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__optionU_e__iso.Interface <+ Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__token__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso.Interface <+ Interface.list__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.prod__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__ImpParser_LF_ImpParser_parseSimpleCommand : imported_nat ->
  imported_list imported_Original_LF__DOT__ImpParser_LF_ImpParser_token ->
  imported_Original_LF__DOT__ImpParser_LF_ImpParser_optionE (imported_prod imported_Original_LF__DOT__Imp_LF_Imp_com (imported_list imported_Original_LF__DOT__ImpParser_LF_ImpParser_token)).
Parameter Original_LF__DOT__ImpParser_LF_ImpParser_parseSimpleCommand_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 ->
  forall (x3 : list Original.LF_DOT_ImpParser.LF.ImpParser.token) (x4 : imported_list imported_Original_LF__DOT__ImpParser_LF_ImpParser_token),
  rel_iso (list_iso Original_LF__DOT__ImpParser_LF_ImpParser_token_iso) x3 x4 ->
  rel_iso (Original_LF__DOT__ImpParser_LF_ImpParser_optionE_iso (prod_iso Original_LF__DOT__Imp_LF_Imp_com_iso (list_iso Original_LF__DOT__ImpParser_LF_ImpParser_token_iso)))
    (Original.LF_DOT_ImpParser.LF.ImpParser.parseSimpleCommand x1 x3) (imported_Original_LF__DOT__ImpParser_LF_ImpParser_parseSimpleCommand x2 x4).
Existing Instance Original_LF__DOT__ImpParser_LF_ImpParser_parseSimpleCommand_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_ImpParser.LF.ImpParser.parseSimpleCommand ?x) => unify x Original_LF__DOT__ImpParser_LF_ImpParser_parseSimpleCommand_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_ImpParser.LF.ImpParser.parseSimpleCommand imported_Original_LF__DOT__ImpParser_LF_ImpParser_parseSimpleCommand ?x) => unify x Original_LF__DOT__ImpParser_LF_ImpParser_parseSimpleCommand_iso; constructor : typeclass_instances.


End Interface.