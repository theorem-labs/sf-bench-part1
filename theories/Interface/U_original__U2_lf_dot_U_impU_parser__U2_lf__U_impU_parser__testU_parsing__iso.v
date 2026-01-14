From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__optionU_e__iso Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__token__iso Interface.U_string__string__iso Interface.list__iso Interface.nat__iso Interface.prod__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__optionU_e__iso Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__token__iso Interface.U_string__string__iso Interface.list__iso Interface.nat__iso Interface.prod__iso.

  Export Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__optionU_e__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__token__iso.CodeBlocks Interface.U_string__string__iso.CodeBlocks Interface.list__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.prod__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__optionU_e__iso.Interface <+ Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__token__iso.Interface <+ Interface.U_string__string__iso.Interface <+ Interface.list__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.prod__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__ImpParser_LF_ImpParser_testParsing : forall x : Type,
  (imported_nat ->
   imported_list imported_Original_LF__DOT__ImpParser_LF_ImpParser_token ->
   imported_Original_LF__DOT__ImpParser_LF_ImpParser_optionE (imported_prod x (imported_list imported_Original_LF__DOT__ImpParser_LF_ImpParser_token))) ->
  imported_String_string -> imported_Original_LF__DOT__ImpParser_LF_ImpParser_optionE (imported_prod x (imported_list imported_Original_LF__DOT__ImpParser_LF_ImpParser_token)).
Parameter Original_LF__DOT__ImpParser_LF_ImpParser_testParsing_iso : forall (x1 x2 : Type) (hx : Iso x1 x2)
    (x3 : nat -> list Original.LF_DOT_ImpParser.LF.ImpParser.token -> Original.LF_DOT_ImpParser.LF.ImpParser.optionE (x1 * list Original.LF_DOT_ImpParser.LF.ImpParser.token))
    (x4 : imported_nat ->
          imported_list imported_Original_LF__DOT__ImpParser_LF_ImpParser_token ->
          imported_Original_LF__DOT__ImpParser_LF_ImpParser_optionE (imported_prod x2 (imported_list imported_Original_LF__DOT__ImpParser_LF_ImpParser_token))),
  (forall (x5 : nat) (x6 : imported_nat),
   rel_iso nat_iso x5 x6 ->
   forall (x7 : list Original.LF_DOT_ImpParser.LF.ImpParser.token) (x8 : imported_list imported_Original_LF__DOT__ImpParser_LF_ImpParser_token),
   rel_iso (list_iso Original_LF__DOT__ImpParser_LF_ImpParser_token_iso) x7 x8 ->
   rel_iso (Original_LF__DOT__ImpParser_LF_ImpParser_optionE_iso (prod_iso hx (list_iso Original_LF__DOT__ImpParser_LF_ImpParser_token_iso))) (x3 x5 x7) (x4 x6 x8)) ->
  forall (x5 : String.string) (x6 : imported_String_string),
  rel_iso String_string_iso x5 x6 ->
  rel_iso (Original_LF__DOT__ImpParser_LF_ImpParser_optionE_iso (prod_iso hx (list_iso Original_LF__DOT__ImpParser_LF_ImpParser_token_iso))) (Original.LF_DOT_ImpParser.LF.ImpParser.testParsing x3 x5)
    (imported_Original_LF__DOT__ImpParser_LF_ImpParser_testParsing x4 x6).
Existing Instance Original_LF__DOT__ImpParser_LF_ImpParser_testParsing_iso.
#[export] Hint Extern 0 (IsoStatementProofFor (@Original.LF_DOT_ImpParser.LF.ImpParser.testParsing) ?x) => unify x Original_LF__DOT__ImpParser_LF_ImpParser_testParsing_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween (@Original.LF_DOT_ImpParser.LF.ImpParser.testParsing) imported_Original_LF__DOT__ImpParser_LF_ImpParser_testParsing ?x) => unify x Original_LF__DOT__ImpParser_LF_ImpParser_testParsing_iso; constructor : typeclass_instances.


End Interface.