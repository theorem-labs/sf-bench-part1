From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__optionU_e__iso Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__token__iso Interface.list__iso Interface.prod__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__optionU_e__iso Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__token__iso Interface.list__iso Interface.prod__iso.

  Export Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__optionU_e__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__token__iso.CodeBlocks Interface.list__iso.CodeBlocks Interface.prod__iso.CodeBlocks.

#[export] Instance: MustUnfold Original.LF_DOT_ImpParser.LF.ImpParser.parser := {}.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__optionU_e__iso.Interface <+ Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__token__iso.Interface <+ Interface.list__iso.Interface <+ Interface.prod__iso.Interface.

Module Type Interface (Import args : Args).

Definition imported_Original_LF__DOT__ImpParser_LF_ImpParser_parser : Type -> Type
  := fun x : Type =>
  imported_list imported_Original_LF__DOT__ImpParser_LF_ImpParser_token ->
  imported_Original_LF__DOT__ImpParser_LF_ImpParser_optionE (imported_prod x (imported_list imported_Original_LF__DOT__ImpParser_LF_ImpParser_token)).
Definition Original_LF__DOT__ImpParser_LF_ImpParser_parser_iso : forall x1 x2 : Type, Iso x1 x2 -> Iso (Original.LF_DOT_ImpParser.LF.ImpParser.parser x1) (imported_Original_LF__DOT__ImpParser_LF_ImpParser_parser x2)
  := fun (x1 x2 : Type) (hx : Iso x1 x2) =>
  IsoArrow (list_iso Original_LF__DOT__ImpParser_LF_ImpParser_token_iso)
    (Original_LF__DOT__ImpParser_LF_ImpParser_optionE_iso (prod_iso hx (list_iso Original_LF__DOT__ImpParser_LF_ImpParser_token_iso))).
Existing Instance Original_LF__DOT__ImpParser_LF_ImpParser_parser_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_ImpParser.LF.ImpParser.parser ?x) => unify x Original_LF__DOT__ImpParser_LF_ImpParser_parser_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_ImpParser.LF.ImpParser.parser imported_Original_LF__DOT__ImpParser_LF_ImpParser_parser ?x) => unify x Original_LF__DOT__ImpParser_LF_ImpParser_parser_iso; constructor : typeclass_instances.


End Interface.