From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__optionU_e__iso Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__token__iso Interface.list__iso Interface.prod__iso Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__parser__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__optionU_e__iso Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__token__iso Interface.list__iso Interface.prod__iso Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__parser__iso.

  Export Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__optionU_e__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__token__iso.CodeBlocks Interface.list__iso.CodeBlocks Interface.prod__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__parser__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__optionU_e__iso.Interface <+ Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__token__iso.Interface <+ Interface.list__iso.Interface <+ Interface.prod__iso.Interface <+ Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__parser__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__ImpParser_LF_ImpParser_firstExpect : forall x : Type,
  imported_Original_LF__DOT__ImpParser_LF_ImpParser_token ->
  (imported_list imported_Original_LF__DOT__ImpParser_LF_ImpParser_token ->
   imported_Original_LF__DOT__ImpParser_LF_ImpParser_optionE (imported_prod x (imported_list imported_Original_LF__DOT__ImpParser_LF_ImpParser_token))) ->
  imported_list imported_Original_LF__DOT__ImpParser_LF_ImpParser_token ->
  imported_Original_LF__DOT__ImpParser_LF_ImpParser_optionE (imported_prod x (imported_list imported_Original_LF__DOT__ImpParser_LF_ImpParser_token)).
Parameter Original_LF__DOT__ImpParser_LF_ImpParser_firstExpect_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_ImpParser.LF.ImpParser.token) (x4 : imported_Original_LF__DOT__ImpParser_LF_ImpParser_token),
  rel_iso Original_LF__DOT__ImpParser_LF_ImpParser_token_iso x3 x4 ->
  forall (x5 : Original.LF_DOT_ImpParser.LF.ImpParser.parser x1)
    (x6 : imported_list imported_Original_LF__DOT__ImpParser_LF_ImpParser_token ->
          imported_Original_LF__DOT__ImpParser_LF_ImpParser_optionE (imported_prod x2 (imported_list imported_Original_LF__DOT__ImpParser_LF_ImpParser_token))),
  (forall (x7 : list Original.LF_DOT_ImpParser.LF.ImpParser.token) (x8 : imported_list imported_Original_LF__DOT__ImpParser_LF_ImpParser_token),
   rel_iso (list_iso Original_LF__DOT__ImpParser_LF_ImpParser_token_iso) x7 x8 ->
   rel_iso (Original_LF__DOT__ImpParser_LF_ImpParser_optionE_iso (prod_iso hx (list_iso Original_LF__DOT__ImpParser_LF_ImpParser_token_iso))) (x5 x7) (x6 x8)) ->
  forall (x7 : list Original.LF_DOT_ImpParser.LF.ImpParser.token) (x8 : imported_list imported_Original_LF__DOT__ImpParser_LF_ImpParser_token),
  rel_iso (list_iso Original_LF__DOT__ImpParser_LF_ImpParser_token_iso) x7 x8 ->
  rel_iso (Original_LF__DOT__ImpParser_LF_ImpParser_optionE_iso (prod_iso hx (list_iso Original_LF__DOT__ImpParser_LF_ImpParser_token_iso)))
    (Original.LF_DOT_ImpParser.LF.ImpParser.firstExpect x3 x5 x7) (imported_Original_LF__DOT__ImpParser_LF_ImpParser_firstExpect x4 x6 x8).
Existing Instance Original_LF__DOT__ImpParser_LF_ImpParser_firstExpect_iso.
#[export] Hint Extern 0 (IsoStatementProofFor (@Original.LF_DOT_ImpParser.LF.ImpParser.firstExpect) ?x) => unify x Original_LF__DOT__ImpParser_LF_ImpParser_firstExpect_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween (@Original.LF_DOT_ImpParser.LF.ImpParser.firstExpect) imported_Original_LF__DOT__ImpParser_LF_ImpParser_firstExpect ?x) => unify x Original_LF__DOT__ImpParser_LF_ImpParser_firstExpect_iso; constructor : typeclass_instances.


End Interface.