From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.nat__iso Interface.U_nat__add__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_evU_playground__ev__iso.

Module Export CodeBlocks.

  Export (hints) Interface.nat__iso Interface.U_nat__add__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_evU_playground__ev__iso.

  Export Interface.nat__iso.CodeBlocks Interface.U_nat__add__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_evU_playground__ev__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.nat__iso.Interface <+ Interface.U_nat__add__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_evU_playground__ev__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_ev__ev____ev : forall x x0 : imported_nat,
  imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (imported_Nat_add x x0) ->
  imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev x -> imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev x0.
Parameter Original_LF__DOT__IndProp_LF_IndProp_ev__ev____ev_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) (x5 : Original.LF_DOT_IndProp.LF.IndProp.EvPlayground.ev (x1 + x3))
    (x6 : imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (imported_Nat_add x2 x4)),
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev_iso (Nat_add_iso hx hx0)) x5 x6 ->
  forall (x7 : Original.LF_DOT_IndProp.LF.IndProp.EvPlayground.ev x1) (x8 : imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev x2),
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev_iso hx) x7 x8 ->
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev_iso hx0) (Original.LF_DOT_IndProp.LF.IndProp.ev_ev__ev x1 x3 x5 x7) (imported_Original_LF__DOT__IndProp_LF_IndProp_ev__ev____ev x6 x8).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_ev__ev____ev_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.ev_ev__ev ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_ev__ev____ev_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.ev_ev__ev imported_Original_LF__DOT__IndProp_LF_IndProp_ev__ev____ev ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_ev__ev____ev_iso; constructor : typeclass_instances.


End Interface.