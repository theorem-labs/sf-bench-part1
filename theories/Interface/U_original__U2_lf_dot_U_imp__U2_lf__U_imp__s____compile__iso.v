From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__sinstr__iso Interface.list__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__sinstr__iso Interface.list__iso.

  Export Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__sinstr__iso.CodeBlocks Interface.list__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__sinstr__iso.Interface <+ Interface.list__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Imp_LF_Imp_s__compile : imported_Original_LF__DOT__Imp_LF_Imp_aexp -> imported_list imported_Original_LF__DOT__Imp_LF_Imp_sinstr.
Parameter Original_LF__DOT__Imp_LF_Imp_s__compile_iso : forall (x1 : Original.LF_DOT_Imp.LF.Imp.aexp) (x2 : imported_Original_LF__DOT__Imp_LF_Imp_aexp),
  rel_iso Original_LF__DOT__Imp_LF_Imp_aexp_iso x1 x2 ->
  rel_iso (list_iso Original_LF__DOT__Imp_LF_Imp_sinstr_iso) (Original.LF_DOT_Imp.LF.Imp.s_compile x1) (imported_Original_LF__DOT__Imp_LF_Imp_s__compile x2).
Existing Instance Original_LF__DOT__Imp_LF_Imp_s__compile_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.s_compile ?x) => unify x Original_LF__DOT__Imp_LF_Imp_s__compile_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.s_compile imported_Original_LF__DOT__Imp_LF_Imp_s__compile ?x) => unify x Original_LF__DOT__Imp_LF_Imp_s__compile_iso; constructor : typeclass_instances.


End Interface.