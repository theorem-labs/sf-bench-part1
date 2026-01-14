From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natlist__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natlist__iso.

  Export Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natlist__iso.CodeBlocks.

#[export] Instance: MustUnfold Original.LF_DOT_Lists.LF.Lists.NatList.bag := {}.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natlist__iso.Args <+ Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natlist__iso.Interface.

Module Type Interface (Import args : Args).

Definition imported_Original_LF__DOT__Lists_LF_Lists_NatList_bag : Type
  := imported_Original_LF__DOT__Lists_LF_Lists_NatList_natlist.
Definition Original_LF__DOT__Lists_LF_Lists_NatList_bag_iso : Iso Original.LF_DOT_Lists.LF.Lists.NatList.bag imported_Original_LF__DOT__Lists_LF_Lists_NatList_bag
  := Original_LF__DOT__Lists_LF_Lists_NatList_natlist_iso.
Existing Instance Original_LF__DOT__Lists_LF_Lists_NatList_bag_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.bag ?x) => unify x Original_LF__DOT__Lists_LF_Lists_NatList_bag_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.bag imported_Original_LF__DOT__Lists_LF_Lists_NatList_bag ?x) => unify x Original_LF__DOT__Lists_LF_Lists_NatList_bag_iso; constructor : typeclass_instances.


End Interface.