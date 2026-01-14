From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natlist__iso Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__rev__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natlist__iso Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__rev__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso.

  Export Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natlist__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__rev__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natlist__iso.Interface <+ Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__rev__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Lists_LF_Lists_NatList_rev__injective : forall x x0 : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist,
  imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Lists_LF_Lists_NatList_rev x) (imported_Original_LF__DOT__Lists_LF_Lists_NatList_rev x0) -> imported_Corelib_Init_Logic_eq x x0.
Parameter Original_LF__DOT__Lists_LF_Lists_NatList_rev__injective_iso : forall (x1 : Original.LF_DOT_Lists.LF.Lists.NatList.natlist) (x2 : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist)
    (hx : rel_iso Original_LF__DOT__Lists_LF_Lists_NatList_natlist_iso x1 x2) (x3 : Original.LF_DOT_Lists.LF.Lists.NatList.natlist) (x4 : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist)
    (hx0 : rel_iso Original_LF__DOT__Lists_LF_Lists_NatList_natlist_iso x3 x4) (x5 : Original.LF_DOT_Lists.LF.Lists.NatList.rev x1 = Original.LF_DOT_Lists.LF.Lists.NatList.rev x3)
    (x6 : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Lists_LF_Lists_NatList_rev x2) (imported_Original_LF__DOT__Lists_LF_Lists_NatList_rev x4)),
  rel_iso (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Lists_LF_Lists_NatList_rev_iso hx) (Original_LF__DOT__Lists_LF_Lists_NatList_rev_iso hx0)) x5 x6 ->
  rel_iso (Corelib_Init_Logic_eq_iso hx hx0) (Original.LF_DOT_Lists.LF.Lists.NatList.rev_injective x1 x3 x5) (imported_Original_LF__DOT__Lists_LF_Lists_NatList_rev__injective x6).
Existing Instance Original_LF__DOT__Lists_LF_Lists_NatList_rev__injective_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.rev_injective ?x) => unify x Original_LF__DOT__Lists_LF_Lists_NatList_rev__injective_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.rev_injective imported_Original_LF__DOT__Lists_LF_Lists_NatList_rev__injective ?x) => unify x Original_LF__DOT__Lists_LF_Lists_NatList_rev__injective_iso; constructor : typeclass_instances.


End Interface.