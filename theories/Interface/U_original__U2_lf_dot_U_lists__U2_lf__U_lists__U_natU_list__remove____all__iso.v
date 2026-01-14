From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natlist__iso Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__bag__iso Interface.nat__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natlist__iso Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__bag__iso Interface.nat__iso.

  Export Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natlist__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__bag__iso.CodeBlocks Interface.nat__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natlist__iso.Interface <+ Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__bag__iso.Interface <+ Interface.nat__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Lists_LF_Lists_NatList_remove__all : imported_nat -> imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist -> imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist.
Parameter Original_LF__DOT__Lists_LF_Lists_NatList_remove__all_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 ->
  forall (x3 : Original.LF_DOT_Lists.LF.Lists.NatList.bag) (x4 : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist),
  rel_iso Original_LF__DOT__Lists_LF_Lists_NatList_natlist_iso x3 x4 ->
  rel_iso Original_LF__DOT__Lists_LF_Lists_NatList_natlist_iso (Original.LF_DOT_Lists.LF.Lists.NatList.remove_all x1 x3) (imported_Original_LF__DOT__Lists_LF_Lists_NatList_remove__all x2 x4).
Existing Instance Original_LF__DOT__Lists_LF_Lists_NatList_remove__all_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.remove_all ?x) => unify x Original_LF__DOT__Lists_LF_Lists_NatList_remove__all_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.remove_all imported_Original_LF__DOT__Lists_LF_Lists_NatList_remove__all ?x) => unify x Original_LF__DOT__Lists_LF_Lists_NatList_remove__all_iso; constructor : typeclass_instances.


End Interface.