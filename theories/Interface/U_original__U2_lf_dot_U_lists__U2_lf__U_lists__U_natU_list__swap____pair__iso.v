From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natprod__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natprod__iso.

  Export Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natprod__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natprod__iso.Args <+ Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natprod__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Lists_LF_Lists_NatList_swap__pair : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natprod -> imported_Original_LF__DOT__Lists_LF_Lists_NatList_natprod.
Parameter Original_LF__DOT__Lists_LF_Lists_NatList_swap__pair_iso : forall (x1 : Original.LF_DOT_Lists.LF.Lists.NatList.natprod) (x2 : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natprod),
  rel_iso Original_LF__DOT__Lists_LF_Lists_NatList_natprod_iso x1 x2 ->
  rel_iso Original_LF__DOT__Lists_LF_Lists_NatList_natprod_iso (Original.LF_DOT_Lists.LF.Lists.NatList.swap_pair x1) (imported_Original_LF__DOT__Lists_LF_Lists_NatList_swap__pair x2).
Existing Instance Original_LF__DOT__Lists_LF_Lists_NatList_swap__pair_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.swap_pair ?x) => unify x Original_LF__DOT__Lists_LF_Lists_NatList_swap__pair_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.swap_pair imported_Original_LF__DOT__Lists_LF_Lists_NatList_swap__pair ?x) => unify x Original_LF__DOT__Lists_LF_Lists_NatList_swap__pair_iso; constructor : typeclass_instances.


End Interface.