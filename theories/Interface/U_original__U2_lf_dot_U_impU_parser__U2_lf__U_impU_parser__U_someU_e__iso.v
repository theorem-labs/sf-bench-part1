From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__optionU_e__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__optionU_e__iso.

  Export Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__optionU_e__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__optionU_e__iso.Args <+ Interface.U_original__U2_lf_dot_U_impU_parser__U2_lf__U_impU_parser__optionU_e__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__ImpParser_LF_ImpParser_SomeE : forall x : Type, x -> imported_Original_LF__DOT__ImpParser_LF_ImpParser_optionE x.
Parameter Original_LF__DOT__ImpParser_LF_ImpParser_SomeE_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2),
  rel_iso hx x3 x4 -> rel_iso (Original_LF__DOT__ImpParser_LF_ImpParser_optionE_iso hx) (Original.LF_DOT_ImpParser.LF.ImpParser.SomeE x3) (imported_Original_LF__DOT__ImpParser_LF_ImpParser_SomeE x4).
Existing Instance Original_LF__DOT__ImpParser_LF_ImpParser_SomeE_iso.
#[export] Hint Extern 0 (IsoStatementProofFor (@Original.LF_DOT_ImpParser.LF.ImpParser.SomeE) ?x) => unify x Original_LF__DOT__ImpParser_LF_ImpParser_SomeE_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween (@Original.LF_DOT_ImpParser.LF.ImpParser.SomeE) imported_Original_LF__DOT__ImpParser_LF_ImpParser_SomeE ?x) => unify x Original_LF__DOT__ImpParser_LF_ImpParser_SomeE_iso; constructor : typeclass_instances.


End Interface.