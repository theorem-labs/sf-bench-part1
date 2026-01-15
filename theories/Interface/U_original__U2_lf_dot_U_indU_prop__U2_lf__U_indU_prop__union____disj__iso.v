From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_union__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__string__iso Interface.iff__iso Interface.or__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_union__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__string__iso Interface.iff__iso Interface.or__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_union__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__string__iso.CodeBlocks Interface.iff__iso.CodeBlocks Interface.or__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_union__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__string__iso.Interface <+ Interface.iff__iso.Interface <+ Interface.or__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_union__disj : forall (x : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii) (x0 x1 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp imported_Ascii_ascii),
  imported_iff (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match x (imported_Original_LF__DOT__IndProp_LF_IndProp_Union x0 x1))
    (imported_or (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match x x0) (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match x x1)).
Parameter Original_LF__DOT__IndProp_LF_IndProp_union__disj_iso : forall (x1 : Original.LF_DOT_IndProp.LF.IndProp.string) (x2 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii)
    (hx : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso Ascii_ascii_iso) x1 x2) (x3 : Original.LF_DOT_IndProp.LF.IndProp.reg_exp Ascii.ascii)
    (x4 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp imported_Ascii_ascii) (hx0 : rel_iso (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso Ascii_ascii_iso) x3 x4)
    (x5 : Original.LF_DOT_IndProp.LF.IndProp.reg_exp Ascii.ascii) (x6 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp imported_Ascii_ascii)
    (hx1 : rel_iso (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso Ascii_ascii_iso) x5 x6),
  rel_iso
    (relax_Iso_Ts_Ps
       (iff_iso (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso hx (Original_LF__DOT__IndProp_LF_IndProp_Union_iso hx0 hx1))
          (or_iso (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso hx hx0) (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso hx hx1))))
    (Original.LF_DOT_IndProp.LF.IndProp.union_disj x1 x3 x5) (imported_Original_LF__DOT__IndProp_LF_IndProp_union__disj x2 x4 x6).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_union__disj_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.union_disj ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_union__disj_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.union_disj imported_Original_LF__DOT__IndProp_LF_IndProp_union__disj ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_union__disj_iso; constructor : typeclass_instances.


End Interface.