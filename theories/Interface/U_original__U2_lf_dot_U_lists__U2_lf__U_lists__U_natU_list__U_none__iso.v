From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natoption__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natoption__iso.

  Export Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natoption__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natoption__iso.Args <+ Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__U_natU_list__natoption__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Lists_LF_Lists_NatList_None : imported_Original_LF__DOT__Lists_LF_Lists_NatList_natoption.
Parameter Original_LF__DOT__Lists_LF_Lists_NatList_None_iso : rel_iso Original_LF__DOT__Lists_LF_Lists_NatList_natoption_iso Original.LF_DOT_Lists.LF.Lists.NatList.None imported_Original_LF__DOT__Lists_LF_Lists_NatList_None.
Existing Instance Original_LF__DOT__Lists_LF_Lists_NatList_None_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.None ?x) => unify x Original_LF__DOT__Lists_LF_Lists_NatList_None_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.None imported_Original_LF__DOT__Lists_LF_Lists_NatList_None ?x) => unify x Original_LF__DOT__Lists_LF_Lists_NatList_None_iso; constructor : typeclass_instances.


End Interface.