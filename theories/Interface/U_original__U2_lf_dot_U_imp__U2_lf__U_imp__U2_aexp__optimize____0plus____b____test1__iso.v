From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__aexp__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_aplus__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bexp__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_bgt__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_bnot__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__optimize____0plus____b__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_anum__iso Interface.U_s__iso Interface.__0__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__aexp__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_aplus__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bexp__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_bgt__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_bnot__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__optimize____0plus____b__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_anum__iso Interface.U_s__iso Interface.__0__iso.

  Export Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__aexp__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_aplus__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bexp__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_bgt__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_bnot__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__optimize____0plus____b__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_anum__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__aexp__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_aplus__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bexp__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_bgt__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_bnot__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__optimize____0plus____b__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_anum__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b__test1 : imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b
       (imported_Original_LF__DOT__Imp_LF_Imp_AExp_BNot
          (imported_Original_LF__DOT__Imp_LF_Imp_AExp_BGt
             (imported_Original_LF__DOT__Imp_LF_Imp_AExp_APlus (imported_Original_LF__DOT__Imp_LF_Imp_AExp_ANum imported_0)
                (imported_Original_LF__DOT__Imp_LF_Imp_AExp_ANum (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0))))))
             (imported_Original_LF__DOT__Imp_LF_Imp_AExp_ANum (imported_S (imported_S (imported_S (iterate1 imported_S 5 imported_0))))))))
    (imported_Original_LF__DOT__Imp_LF_Imp_AExp_BNot
       (imported_Original_LF__DOT__Imp_LF_Imp_AExp_BGt (imported_Original_LF__DOT__Imp_LF_Imp_AExp_ANum (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0)))))
          (imported_Original_LF__DOT__Imp_LF_Imp_AExp_ANum (imported_S (imported_S (imported_S (iterate1 imported_S 5 imported_0))))))).
Parameter Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b__test1_iso : rel_iso
    (Corelib_Init_Logic_eq_iso
       (Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b_iso
          (Original_LF__DOT__Imp_LF_Imp_AExp_BNot_iso
             (Original_LF__DOT__Imp_LF_Imp_AExp_BGt_iso
                (Original_LF__DOT__Imp_LF_Imp_AExp_APlus_iso (Original_LF__DOT__Imp_LF_Imp_AExp_ANum_iso _0_iso)
                   (Original_LF__DOT__Imp_LF_Imp_AExp_ANum_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 1 0 imported_0 _0_iso))))))
                (Original_LF__DOT__Imp_LF_Imp_AExp_ANum_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 5 0 imported_0 _0_iso))))))))
       (Original_LF__DOT__Imp_LF_Imp_AExp_BNot_iso
          (Original_LF__DOT__Imp_LF_Imp_AExp_BGt_iso (Original_LF__DOT__Imp_LF_Imp_AExp_ANum_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 1 0 imported_0 _0_iso)))))
             (Original_LF__DOT__Imp_LF_Imp_AExp_ANum_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 5 0 imported_0 _0_iso))))))))
    Original.LF_DOT_Imp.LF.Imp.AExp.optimize_0plus_b_test1 imported_Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b__test1.
Existing Instance Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b__test1_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.AExp.optimize_0plus_b_test1 ?x) => unify x Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b__test1_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.AExp.optimize_0plus_b_test1 imported_Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b__test1 ?x) => unify x Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b__test1_iso; constructor : typeclass_instances.


End Interface.