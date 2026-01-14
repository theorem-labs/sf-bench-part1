From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__aexp__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_aplus__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bexp__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_band__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_ble__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_btrue__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__optimize____0plus____b__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_anum__iso Interface.U_s__iso Interface.__0__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__aexp__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_aplus__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bexp__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_band__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_ble__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_btrue__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__optimize____0plus____b__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_anum__iso Interface.U_s__iso Interface.__0__iso.

  Export Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__aexp__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_aplus__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bexp__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_band__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_ble__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_btrue__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__optimize____0plus____b__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_anum__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__aexp__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_aplus__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bexp__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_band__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_ble__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_btrue__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__optimize____0plus____b__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__U2_anum__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b__test2 : imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b
       (imported_Original_LF__DOT__Imp_LF_Imp_AExp_BAnd
          (imported_Original_LF__DOT__Imp_LF_Imp_AExp_BLe
             (imported_Original_LF__DOT__Imp_LF_Imp_AExp_APlus (imported_Original_LF__DOT__Imp_LF_Imp_AExp_ANum imported_0)
                (imported_Original_LF__DOT__Imp_LF_Imp_AExp_ANum (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0))))))
             (imported_Original_LF__DOT__Imp_LF_Imp_AExp_ANum (imported_S (imported_S (imported_S (iterate1 imported_S 2 imported_0))))))
          imported_Original_LF__DOT__Imp_LF_Imp_AExp_BTrue))
    (imported_Original_LF__DOT__Imp_LF_Imp_AExp_BAnd
       (imported_Original_LF__DOT__Imp_LF_Imp_AExp_BLe (imported_Original_LF__DOT__Imp_LF_Imp_AExp_ANum (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0)))))
          (imported_Original_LF__DOT__Imp_LF_Imp_AExp_ANum (imported_S (imported_S (imported_S (iterate1 imported_S 2 imported_0))))))
       imported_Original_LF__DOT__Imp_LF_Imp_AExp_BTrue).
Parameter Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b__test2_iso : rel_iso
    (Corelib_Init_Logic_eq_iso
       (Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b_iso
          (Original_LF__DOT__Imp_LF_Imp_AExp_BAnd_iso
             (Original_LF__DOT__Imp_LF_Imp_AExp_BLe_iso
                (Original_LF__DOT__Imp_LF_Imp_AExp_APlus_iso (Original_LF__DOT__Imp_LF_Imp_AExp_ANum_iso _0_iso)
                   (Original_LF__DOT__Imp_LF_Imp_AExp_ANum_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 1 0 imported_0 _0_iso))))))
                (Original_LF__DOT__Imp_LF_Imp_AExp_ANum_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 2 0 imported_0 _0_iso))))))
             Original_LF__DOT__Imp_LF_Imp_AExp_BTrue_iso))
       (Original_LF__DOT__Imp_LF_Imp_AExp_BAnd_iso
          (Original_LF__DOT__Imp_LF_Imp_AExp_BLe_iso (Original_LF__DOT__Imp_LF_Imp_AExp_ANum_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 1 0 imported_0 _0_iso)))))
             (Original_LF__DOT__Imp_LF_Imp_AExp_ANum_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 2 0 imported_0 _0_iso))))))
          Original_LF__DOT__Imp_LF_Imp_AExp_BTrue_iso))
    Original.LF_DOT_Imp.LF.Imp.AExp.optimize_0plus_b_test2 imported_Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b__test2.
Existing Instance Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b__test2_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.AExp.optimize_0plus_b_test2 ?x) => unify x Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b__test2_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.AExp.optimize_0plus_b_test2 imported_Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b__test2 ?x) => unify x Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b__test2_iso; constructor : typeclass_instances.


End Interface.