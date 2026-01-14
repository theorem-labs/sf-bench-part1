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

Parameter imported_Original_LF__DOT__AltAuto_LF_AltAuto_constructor__example : forall x : imported_nat, imported_Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (imported_Nat_add x x).
Parameter Original_LF__DOT__AltAuto_LF_AltAuto_constructor__example_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2),
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev_iso (Nat_add_iso hx hx)) (Original.LF_DOT_AltAuto.LF.AltAuto.constructor_example x1)
    (imported_Original_LF__DOT__AltAuto_LF_AltAuto_constructor__example x2).
Existing Instance Original_LF__DOT__AltAuto_LF_AltAuto_constructor__example_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.constructor_example ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_constructor__example_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.constructor_example imported_Original_LF__DOT__AltAuto_LF_AltAuto_constructor__example ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_constructor__example_iso; constructor : typeclass_instances.


End Interface.