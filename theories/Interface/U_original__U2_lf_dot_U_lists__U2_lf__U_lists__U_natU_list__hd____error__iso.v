From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natlist__iso Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natoption__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natlist__iso Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natoption__iso.

  Export Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natlist__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natoption__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natlist__iso.Interface <+ Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natoption__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Lists_LF_Lists_NatList_hd__error : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist -> imported_Original_LF__DOT__Lists_LF_Lists_NatList_natoption.
Parameter Original_LF__DOT__Lists_LF_Lists_NatList_hd__error_iso : forall (x1 : Original.LF_DOT_Lists.LF.Lists.NatList.natlist) (x2 : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist),
  rel_iso Original_LF__DOT__Lists_LF_Lists_NatList_natlist_iso x1 x2 ->
  rel_iso Original_LF__DOT__Lists_LF_Lists_NatList_natoption_iso (Original.LF_DOT_Lists.LF.Lists.NatList.hd_error x1) (imported_Original_LF__DOT__Lists_LF_Lists_NatList_hd__error x2).
Existing Instance Original_LF__DOT__Lists_LF_Lists_NatList_hd__error_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.hd_error ?x) => unify x Original_LF__DOT__Lists_LF_Lists_NatList_hd__error_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.hd_error imported_Original_LF__DOT__Lists_LF_Lists_NatList_hd__error ?x) => unify x Original_LF__DOT__Lists_LF_Lists_NatList_hd__error_iso; constructor : typeclass_instances.


End Interface.