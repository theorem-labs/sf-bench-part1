From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_false__iso Interface.U_logic__not__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_emptyU_set__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_false__iso Interface.U_logic__not__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_emptyU_set__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso.

  Export Interface.U_false__iso.CodeBlocks Interface.U_logic__not__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_emptyU_set__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_false__iso.Interface <+ Interface.U_logic__not__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_emptyU_set__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_EmptySet__is__empty : forall (x : Type) (x0 : imported_Original_LF__DOT__Poly_LF_Poly_list x),
  imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match x0 (imported_Original_LF__DOT__IndProp_LF_IndProp_EmptySet x) -> imported_False.
Parameter Original_LF__DOT__IndProp_LF_IndProp_EmptySet__is__empty_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_Poly.LF.Poly.list x1) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2)
    (hx0 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x3 x4) (x5 : Original.LF_DOT_IndProp.LF.IndProp.exp_match x3 Original.LF_DOT_IndProp.LF.IndProp.EmptySet)
    (x6 : imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match x4 (imported_Original_LF__DOT__IndProp_LF_IndProp_EmptySet x2)),
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso hx0 (Original_LF__DOT__IndProp_LF_IndProp_EmptySet_iso hx)) x5 x6 ->
  rel_iso False_iso (Original.LF_DOT_IndProp.LF.IndProp.EmptySet_is_empty x1 x3 x5) (imported_Original_LF__DOT__IndProp_LF_IndProp_EmptySet__is__empty x6).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_EmptySet__is__empty_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.EmptySet_is_empty ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_EmptySet__is__empty_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.EmptySet_is_empty imported_Original_LF__DOT__IndProp_LF_IndProp_EmptySet__is__empty ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_EmptySet__is__empty_iso; constructor : typeclass_instances.


End Interface.