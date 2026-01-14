From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso Interface.bool__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso Interface.bool__iso.

  Export Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso.CodeBlocks Interface.bool__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso.Interface <+ Interface.bool__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Imp_LF_Imp_no__whiles : imported_Original_LF__DOT__Imp_LF_Imp_com -> imported_bool.
Parameter Original_LF__DOT__Imp_LF_Imp_no__whiles_iso : forall (x1 : Original.LF_DOT_Imp.LF.Imp.com) (x2 : imported_Original_LF__DOT__Imp_LF_Imp_com),
  rel_iso Original_LF__DOT__Imp_LF_Imp_com_iso x1 x2 -> rel_iso bool_iso (Original.LF_DOT_Imp.LF.Imp.no_whiles x1) (imported_Original_LF__DOT__Imp_LF_Imp_no__whiles x2).
Existing Instance Original_LF__DOT__Imp_LF_Imp_no__whiles_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.no_whiles ?x) => unify x Original_LF__DOT__Imp_LF_Imp_no__whiles_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.no_whiles imported_Original_LF__DOT__Imp_LF_Imp_no__whiles ?x) => unify x Original_LF__DOT__Imp_LF_Imp_no__whiles_iso; constructor : typeclass_instances.


End Interface.