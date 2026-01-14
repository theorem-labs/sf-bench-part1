From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reflect__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__match____eps__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__refl____matches____eps__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reflect__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__match____eps__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__refl____matches____eps__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reflect__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__match____eps__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__refl____matches____eps__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reflect__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__match____eps__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__refl____matches____eps__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_match__eps__refl : forall x : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp imported_Ascii_ascii,
  imported_Original_LF__DOT__IndProp_LF_IndProp_reflect (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_Ascii_ascii) x)
    (imported_Original_LF__DOT__IndProp_LF_IndProp_match__eps x).
Parameter Original_LF__DOT__IndProp_LF_IndProp_match__eps__refl_iso : forall (x1 : Original.LF_DOT_IndProp.LF.IndProp.reg_exp Ascii.ascii) (x2 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp imported_Ascii_ascii)
    (hx : rel_iso (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso Ascii_ascii_iso) x1 x2),
  rel_iso
    {|
      to :=
        Original_LF__DOT__IndProp_LF_IndProp_reflect_iso (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso (Original_LF__DOT__Poly_LF_Poly_nil_iso Ascii_ascii_iso) hx)
          (Original_LF__DOT__IndProp_LF_IndProp_match__eps_iso hx);
      from :=
        from
          (Original_LF__DOT__IndProp_LF_IndProp_reflect_iso (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso (Original_LF__DOT__Poly_LF_Poly_nil_iso Ascii_ascii_iso) hx)
             (Original_LF__DOT__IndProp_LF_IndProp_match__eps_iso hx));
      to_from :=
        fun
          x : imported_Original_LF__DOT__IndProp_LF_IndProp_reflect (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_Ascii_ascii) x2)
                (imported_Original_LF__DOT__IndProp_LF_IndProp_match__eps x2) =>
        to_from
          (Original_LF__DOT__IndProp_LF_IndProp_reflect_iso (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso (Original_LF__DOT__Poly_LF_Poly_nil_iso Ascii_ascii_iso) hx)
             (Original_LF__DOT__IndProp_LF_IndProp_match__eps_iso hx))
          x;
      from_to :=
        fun x : Original.LF_DOT_IndProp.LF.IndProp.reflect (Original.LF_DOT_IndProp.LF.IndProp.exp_match Original.LF_DOT_Poly.LF.Poly.nil x1) (Original.LF_DOT_IndProp.LF.IndProp.match_eps x1) =>
        seq_p_of_t
          (from_to
             (Original_LF__DOT__IndProp_LF_IndProp_reflect_iso (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso (Original_LF__DOT__Poly_LF_Poly_nil_iso Ascii_ascii_iso) hx)
                (Original_LF__DOT__IndProp_LF_IndProp_match__eps_iso hx))
             x)
    |} (Original.LF_DOT_IndProp.LF.IndProp.match_eps_refl x1) (imported_Original_LF__DOT__IndProp_LF_IndProp_match__eps__refl x2).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_match__eps__refl_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.match_eps_refl ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_match__eps__refl_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.match_eps_refl imported_Original_LF__DOT__IndProp_LF_IndProp_match__eps__refl ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_match__eps__refl_iso; constructor : typeclass_instances.


End Interface.