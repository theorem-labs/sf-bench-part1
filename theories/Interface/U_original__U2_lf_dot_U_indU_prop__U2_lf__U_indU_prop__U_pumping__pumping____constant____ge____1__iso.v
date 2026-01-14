From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_pumping__pumping____constant__iso Interface.U_s__iso Interface.__0__iso Interface.ge__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_pumping__pumping____constant__iso Interface.U_s__iso Interface.__0__iso Interface.ge__iso.

  Export Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_pumping__pumping____constant__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks Interface.ge__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_pumping__pumping____constant__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface <+ Interface.ge__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant__ge__1 : forall (x : Type) (x0 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp x), imported_ge (imported_Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant x0) (imported_S imported_0).
Parameter Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant__ge__1_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_IndProp.LF.IndProp.reg_exp x1) (x4 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp x2)
    (hx0 : rel_iso (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) x3 x4),
  rel_iso (ge_iso (Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant_iso hx0) (S_iso _0_iso)) (Original.LF_DOT_IndProp.LF.IndProp.Pumping.pumping_constant_ge_1 x1 x3)
    (imported_Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant__ge__1 x4).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant__ge__1_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.Pumping.pumping_constant_ge_1 ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant__ge__1_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.Pumping.pumping_constant_ge_1 imported_Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant__ge__1 ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant__ge__1_iso; constructor : typeclass_instances.


End Interface.