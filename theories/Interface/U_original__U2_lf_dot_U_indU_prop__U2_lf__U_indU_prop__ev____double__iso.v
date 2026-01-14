From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.nat__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_evU_playground__ev__iso Interface.U_original__U2_lf_dot_U_induction__U2_lf__U_induction__double__iso.

Module Export CodeBlocks.

  Export (hints) Interface.nat__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_evU_playground__ev__iso Interface.U_original__U2_lf_dot_U_induction__U2_lf__U_induction__double__iso.

  Export Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_evU_playground__ev__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_induction__U2_lf__U_induction__double__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_evU_playground__ev__iso.Interface <+ Interface.U_original__U2_lf_dot_U_induction__U2_lf__U_induction__double__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_ev__double : forall x : imported_nat, imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (imported_Original_LF__DOT__Induction_LF_Induction_double x).
Parameter Original_LF__DOT__IndProp_LF_IndProp_ev__double_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2),
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev_iso (Original_LF__DOT__Induction_LF_Induction_double_iso hx)) (Original.LF_DOT_IndProp.LF.IndProp.ev_double x1)
    (imported_Original_LF__DOT__IndProp_LF_IndProp_ev__double x2).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_ev__double_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.ev_double ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_ev__double_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.ev_double imported_Original_LF__DOT__IndProp_LF_IndProp_ev__double ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_ev__double_iso; constructor : typeclass_instances.


End Interface.