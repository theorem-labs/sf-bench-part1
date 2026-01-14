From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_false__iso Interface.U_logic__not__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_evU_playground__ev__iso Interface.U_s__iso Interface.__0__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_false__iso Interface.U_logic__not__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_evU_playground__ev__iso Interface.U_s__iso Interface.__0__iso.

  Export Interface.U_false__iso.CodeBlocks Interface.U_logic__not__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_evU_playground__ev__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_false__iso.Interface <+ Interface.U_logic__not__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_evU_playground__ev__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_one__not__even' : imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (imported_S imported_0) -> imported_False.
Parameter Original_LF__DOT__IndProp_LF_IndProp_one__not__even'_iso : forall (x1 : Original.LF_DOT_IndProp.LF.IndProp.EvPlayground.ev 1) (x2 : imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (imported_S imported_0)),
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev_iso (S_iso _0_iso)) x1 x2 ->
  rel_iso False_iso (Original.LF_DOT_IndProp.LF.IndProp.one_not_even' x1) (imported_Original_LF__DOT__IndProp_LF_IndProp_one__not__even' x2).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_one__not__even'_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.one_not_even' ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_one__not__even'_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.one_not_even' imported_Original_LF__DOT__IndProp_LF_IndProp_one__not__even' ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_one__not__even'_iso; constructor : typeclass_instances.


End Interface.