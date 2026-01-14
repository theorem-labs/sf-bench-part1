From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__sinstr__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__sinstr__iso.

  Export Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__sinstr__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__sinstr__iso.Args <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__sinstr__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Imp_LF_Imp_SMult : imported_Original_LF__DOT__Imp_LF_Imp_sinstr.
Parameter Original_LF__DOT__Imp_LF_Imp_SMult_iso : rel_iso Original_LF__DOT__Imp_LF_Imp_sinstr_iso Original.LF_DOT_Imp.LF.Imp.SMult imported_Original_LF__DOT__Imp_LF_Imp_SMult.
Existing Instance Original_LF__DOT__Imp_LF_Imp_SMult_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.SMult ?x) => unify x Original_LF__DOT__Imp_LF_Imp_SMult_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.SMult imported_Original_LF__DOT__Imp_LF_Imp_SMult ?x) => unify x Original_LF__DOT__Imp_LF_Imp_SMult_iso; constructor : typeclass_instances.


End Interface.