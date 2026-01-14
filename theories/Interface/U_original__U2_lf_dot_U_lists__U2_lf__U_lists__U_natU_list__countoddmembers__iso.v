From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natlist__iso Interface.nat__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natlist__iso Interface.nat__iso.

  Export Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natlist__iso.CodeBlocks Interface.nat__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natlist__iso.Interface <+ Interface.nat__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Lists_LF_Lists_NatList_countoddmembers : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist -> imported_nat.
Parameter Original_LF__DOT__Lists_LF_Lists_NatList_countoddmembers_iso : forall (x1 : Original.LF_DOT_Lists.LF.Lists.NatList.natlist) (x2 : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist),
  rel_iso Original_LF__DOT__Lists_LF_Lists_NatList_natlist_iso x1 x2 ->
  rel_iso nat_iso (Original.LF_DOT_Lists.LF.Lists.NatList.countoddmembers x1) (imported_Original_LF__DOT__Lists_LF_Lists_NatList_countoddmembers x2).
Existing Instance Original_LF__DOT__Lists_LF_Lists_NatList_countoddmembers_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.countoddmembers ?x) => unify x Original_LF__DOT__Lists_LF_Lists_NatList_countoddmembers_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.countoddmembers imported_Original_LF__DOT__Lists_LF_Lists_NatList_countoddmembers ?x) => unify x Original_LF__DOT__Lists_LF_Lists_NatList_countoddmembers_iso; constructor : typeclass_instances.


End Interface.