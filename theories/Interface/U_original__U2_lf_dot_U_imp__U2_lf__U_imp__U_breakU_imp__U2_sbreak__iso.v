From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__result__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__result__iso.

  Export Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__result__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__result__iso.Args <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__result__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_SBreak : imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_result.
Parameter Original_LF__DOT__Imp_LF_Imp_BreakImp_SBreak_iso : rel_iso Original_LF__DOT__Imp_LF_Imp_BreakImp_result_iso Original.LF_DOT_Imp.LF.Imp.BreakImp.SBreak imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_SBreak.
Existing Instance Original_LF__DOT__Imp_LF_Imp_BreakImp_SBreak_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.BreakImp.SBreak ?x) => unify x Original_LF__DOT__Imp_LF_Imp_BreakImp_SBreak_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.BreakImp.SBreak imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_SBreak ?x) => unify x Original_LF__DOT__Imp_LF_Imp_BreakImp_SBreak_iso; constructor : typeclass_instances.


End Interface.