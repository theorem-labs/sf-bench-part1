From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__com__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__bexp__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__com__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__bexp__iso.

  Export Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__com__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__bexp__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__com__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__bexp__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_CWhile : imported_Original_LF__DOT__Imp_LF_Imp_bexp -> imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_com -> imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_com.
Parameter Original_LF__DOT__Imp_LF_Imp_BreakImp_CWhile_iso : forall (x1 : Original.LF_DOT_Imp.LF.Imp.bexp) (x2 : imported_Original_LF__DOT__Imp_LF_Imp_bexp),
  rel_iso Original_LF__DOT__Imp_LF_Imp_bexp_iso x1 x2 ->
  forall (x3 : Original.LF_DOT_Imp.LF.Imp.BreakImp.com) (x4 : imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_com),
  rel_iso Original_LF__DOT__Imp_LF_Imp_BreakImp_com_iso x3 x4 ->
  rel_iso Original_LF__DOT__Imp_LF_Imp_BreakImp_com_iso (Original.LF_DOT_Imp.LF.Imp.BreakImp.CWhile x1 x3) (imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_CWhile x2 x4).
Existing Instance Original_LF__DOT__Imp_LF_Imp_BreakImp_CWhile_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.BreakImp.CWhile ?x) => unify x Original_LF__DOT__Imp_LF_Imp_BreakImp_CWhile_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.BreakImp.CWhile imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_CWhile ?x) => unify x Original_LF__DOT__Imp_LF_Imp_BreakImp_CWhile_iso; constructor : typeclass_instances.


End Interface.