From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.iff__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_evU_playground__ev__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__evSQUOTE__iso.

Module Export CodeBlocks.

  Export (hints) Interface.iff__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_evU_playground__ev__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__evSQUOTE__iso.

  Export Interface.iff__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_evU_playground__ev__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__evSQUOTE__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.iff__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_evU_playground__ev__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__evSQUOTE__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_ev'__ev : forall x : imported_nat, imported_iff (imported_Original_LF__DOT__IndProp_LF_IndProp_ev' x) (imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev x).
Parameter Original_LF__DOT__IndProp_LF_IndProp_ev'__ev_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2),
  rel_iso (relax_Iso_Ts_Ps (iff_iso (Original_LF__DOT__IndProp_LF_IndProp_ev'_iso hx) (Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev_iso hx))) (Original.LF_DOT_IndProp.LF.IndProp.ev'_ev x1)
    (imported_Original_LF__DOT__IndProp_LF_IndProp_ev'__ev x2).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_ev'__ev_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.ev'_ev ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_ev'__ev_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.ev'_ev imported_Original_LF__DOT__IndProp_LF_IndProp_ev'__ev ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_ev'__ev_iso; constructor : typeclass_instances.


End Interface.