From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U_false__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_pumping__pumping____constant__iso Interface.__0__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U_false__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_pumping__pumping____constant__iso Interface.__0__iso.

  Export Interface.U_original__U_false__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_pumping__pumping____constant__iso.CodeBlocks Interface.__0__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U_false__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_pumping__pumping____constant__iso.Interface <+ Interface.__0__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant__0__false : forall (x : Type) (x0 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp x),
  imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant x0) imported_0 -> imported_Original_False.
Parameter Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant__0__false_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_IndProp.LF.IndProp.reg_exp x1) (x4 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp x2)
    (hx0 : rel_iso (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) x3 x4) (x5 : Original.LF_DOT_IndProp.LF.IndProp.Pumping.pumping_constant x3 = 0)
    (x6 : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant x4) imported_0),
  rel_iso (Corelib_Init_Logic_eq_iso (Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant_iso hx0) _0_iso) x5 x6 ->
  rel_iso Original_False_iso (Original.LF_DOT_IndProp.LF.IndProp.Pumping.pumping_constant_0_false x1 x3 x5) (imported_Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant__0__false x6).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant__0__false_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.Pumping.pumping_constant_0_false ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant__0__false_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.Pumping.pumping_constant_0_false imported_Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant__0__false ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant__0__false_iso; constructor : typeclass_instances.


End Interface.