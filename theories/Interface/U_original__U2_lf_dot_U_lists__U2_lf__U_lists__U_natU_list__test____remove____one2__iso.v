From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natlist__iso Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__bag__iso Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__nil__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__cons__iso Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__count__iso Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__remove____one__iso Interface.U_s__iso Interface.__0__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natlist__iso Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__bag__iso Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__nil__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__cons__iso Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__count__iso Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__remove____one__iso Interface.U_s__iso Interface.__0__iso.

  Export Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natlist__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__bag__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__nil__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__cons__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__count__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__remove____one__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natlist__iso.Interface <+ Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__bag__iso.Interface <+ Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__nil__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__cons__iso.Interface <+ Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__count__iso.Interface <+ Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__remove____one__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Lists_LF_Lists_NatList_test__remove__one2 : imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Lists_LF_Lists_NatList_count (imported_S (imported_S (imported_S (iterate1 imported_S 2 imported_0))))
       (imported_Original_LF__DOT__Lists_LF_Lists_NatList_remove__one (imported_S (imported_S (imported_S (iterate1 imported_S 2 imported_0))))
          (imported_Original_LF__DOT__Lists_LF_Lists_NatList_cons (imported_S (imported_S imported_0))
             (imported_Original_LF__DOT__Lists_LF_Lists_NatList_cons (imported_S imported_0)
                (imported_Original_LF__DOT__Lists_LF_Lists_NatList_cons (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0))))
                   (imported_Original_LF__DOT__Lists_LF_Lists_NatList_cons (imported_S imported_0) imported_Original_LF__DOT__Lists_LF_Lists_NatList_nil))))))
    imported_0.
Parameter Original_LF__DOT__Lists_LF_Lists_NatList_test__remove__one2_iso : rel_iso
    (Corelib_Init_Logic_eq_iso
       (Original_LF__DOT__Lists_LF_Lists_NatList_count_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 2 0 imported_0 _0_iso))))
          (Original_LF__DOT__Lists_LF_Lists_NatList_remove__one_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 2 0 imported_0 _0_iso))))
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso _0_iso))
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso _0_iso)
                   (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 1 0 imported_0 _0_iso))))
                      (Original_LF__DOT__Lists_LF_Lists_NatList_cons_iso (S_iso _0_iso) Original_LF__DOT__Lists_LF_Lists_NatList_nil_iso))))))
       _0_iso)
    Original.LF_DOT_Lists.LF.Lists.NatList.test_remove_one2 imported_Original_LF__DOT__Lists_LF_Lists_NatList_test__remove__one2.
Existing Instance Original_LF__DOT__Lists_LF_Lists_NatList_test__remove__one2_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.test_remove_one2 ?x) => unify x Original_LF__DOT__Lists_LF_Lists_NatList_test__remove__one2_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.test_remove_one2 imported_Original_LF__DOT__Lists_LF_Lists_NatList_test__remove__one2 ?x) => unify x Original_LF__DOT__Lists_LF_Lists_NatList_test__remove__one2_iso; constructor : typeclass_instances.


End Interface.