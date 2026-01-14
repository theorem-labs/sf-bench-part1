From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.

  Export Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.Args <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__AltAuto_LF_AltAuto_re__opt : forall x : Type, imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp x -> imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp x.
Parameter Original_LF__DOT__AltAuto_LF_AltAuto_re__opt_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_IndProp.LF.IndProp.reg_exp x1) (x4 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp x2),
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) x3 x4 ->
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) (Original.LF_DOT_AltAuto.LF.AltAuto.re_opt x3) (imported_Original_LF__DOT__AltAuto_LF_AltAuto_re__opt x4).
Existing Instance Original_LF__DOT__AltAuto_LF_AltAuto_re__opt_iso.
#[export] Hint Extern 0 (IsoStatementProofFor (@Original.LF_DOT_AltAuto.LF.AltAuto.re_opt) ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_re__opt_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween (@Original.LF_DOT_AltAuto.LF.AltAuto.re_opt) imported_Original_LF__DOT__AltAuto_LF_AltAuto_re__opt ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_re__opt_iso; constructor : typeclass_instances.


End Interface.