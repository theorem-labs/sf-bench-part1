From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__no____whilesU_r__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__no____whiles__iso Interface.iff__iso Interface.true__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__no____whilesU_r__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__no____whiles__iso Interface.iff__iso Interface.true__iso.

  Export Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__no____whilesU_r__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.bool__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__no____whiles__iso.CodeBlocks Interface.iff__iso.CodeBlocks Interface.true__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__no____whilesU_r__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.bool__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__no____whiles__iso.Interface <+ Interface.iff__iso.Interface <+ Interface.true__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Imp_LF_Imp_no__whiles__eqv : forall x : imported_Original_LF__DOT__Imp_LF_Imp_com,
  imported_iff (imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Imp_LF_Imp_no__whiles x) imported_true) (imported_Original_LF__DOT__Imp_LF_Imp_no__whilesR x).
Parameter Original_LF__DOT__Imp_LF_Imp_no__whiles__eqv_iso : forall (x1 : Original.LF_DOT_Imp.LF.Imp.com) (x2 : imported_Original_LF__DOT__Imp_LF_Imp_com) (hx : rel_iso Original_LF__DOT__Imp_LF_Imp_com_iso x1 x2),
  rel_iso (relax_Iso_Ts_Ps (iff_iso (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Imp_LF_Imp_no__whiles_iso hx) true_iso) (Original_LF__DOT__Imp_LF_Imp_no__whilesR_iso hx)))
    (Original.LF_DOT_Imp.LF.Imp.no_whiles_eqv x1) (imported_Original_LF__DOT__Imp_LF_Imp_no__whiles__eqv x2).
Existing Instance Original_LF__DOT__Imp_LF_Imp_no__whiles__eqv_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.no_whiles_eqv ?x) => unify x Original_LF__DOT__Imp_LF_Imp_no__whiles__eqv_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.no_whiles_eqv imported_Original_LF__DOT__Imp_LF_Imp_no__whiles__eqv ?x) => unify x Original_LF__DOT__Imp_LF_Imp_no__whiles__eqv_iso; constructor : typeclass_instances.


End Interface.