From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.nat__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_evU_playground__ev__iso Interface.U_s__iso.

Module Export CodeBlocks.

  Export (hints) Interface.nat__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_evU_playground__ev__iso Interface.U_s__iso.

  Export Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_evU_playground__ev__iso.CodeBlocks Interface.U_s__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_evU_playground__ev__iso.Interface <+ Interface.U_s__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_evSS__ev : forall x : imported_nat, imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (imported_S (imported_S x)) -> imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev x.
Parameter Original_LF__DOT__IndProp_LF_IndProp_evSS__ev_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : Original.LF_DOT_IndProp.LF.IndProp.EvPlayground.ev (S (S x1)))
    (x4 : imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (imported_S (imported_S x2))),
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev_iso (S_iso (S_iso hx))) x3 x4 ->
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev_iso hx) (Original.LF_DOT_IndProp.LF.IndProp.evSS_ev x1 x3) (imported_Original_LF__DOT__IndProp_LF_IndProp_evSS__ev x4).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_evSS__ev_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.evSS_ev ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_evSS__ev_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.evSS_ev imported_Original_LF__DOT__IndProp_LF_IndProp_evSS__ev ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_evSS__ev_iso; constructor : typeclass_instances.


End Interface.