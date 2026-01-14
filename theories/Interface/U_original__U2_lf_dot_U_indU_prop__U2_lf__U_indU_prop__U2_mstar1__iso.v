From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_star__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_star__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso.

  Export Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_star__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_star__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_MStar1 : forall (x : Type) (x0 : imported_Original_LF__DOT__Poly_LF_Poly_list x) (x1 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp x),
  imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match x0 x1 -> imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match x0 (imported_Original_LF__DOT__IndProp_LF_IndProp_Star x1).
Parameter Original_LF__DOT__IndProp_LF_IndProp_MStar1_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_Poly.LF.Poly.list x1) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2)
    (hx0 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x3 x4) (x5 : Original.LF_DOT_IndProp.LF.IndProp.reg_exp x1) (x6 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp x2)
    (hx1 : rel_iso (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) x5 x6) (x7 : Original.LF_DOT_IndProp.LF.IndProp.exp_match x3 x5)
    (x8 : imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match x4 x6),
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso hx0 hx1) x7 x8 ->
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso hx0 (Original_LF__DOT__IndProp_LF_IndProp_Star_iso hx1)) (Original.LF_DOT_IndProp.LF.IndProp.MStar1 x1 x3 x5 x7)
    (imported_Original_LF__DOT__IndProp_LF_IndProp_MStar1 x8).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_MStar1_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.MStar1 ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_MStar1_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.MStar1 imported_Original_LF__DOT__IndProp_LF_IndProp_MStar1 ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_MStar1_iso; constructor : typeclass_instances.


End Interface.