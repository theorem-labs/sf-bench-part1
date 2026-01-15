From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_app__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__string__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.and__iso Interface.ex__iso Interface.iff__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_app__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__string__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.and__iso Interface.ex__iso Interface.iff__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_app__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__string__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.and__iso.CodeBlocks Interface.ex__iso.CodeBlocks Interface.iff__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_app__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__string__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.and__iso.Interface <+ Interface.ex__iso.Interface <+ Interface.iff__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_app__exists : forall (x : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii) (x0 x1 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp imported_Ascii_ascii),
  imported_iff (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match x (imported_Original_LF__DOT__IndProp_LF_IndProp_App x0 x1))
    (imported_ex
       (fun H : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii =>
        imported_ex
          (fun H0 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii =>
           imported_and (imported_Corelib_Init_Logic_eq x (imported_Original_LF__DOT__Poly_LF_Poly_app H H0))
             (imported_and (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match H x0) (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match H0 x1))))).
Parameter Original_LF__DOT__IndProp_LF_IndProp_app__exists_iso : forall (x1 : Original.LF_DOT_IndProp.LF.IndProp.string) (x2 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii)
    (hx : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso Ascii_ascii_iso) x1 x2) (x3 : Original.LF_DOT_IndProp.LF.IndProp.reg_exp Ascii.ascii)
    (x4 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp imported_Ascii_ascii) (hx0 : rel_iso (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso Ascii_ascii_iso) x3 x4)
    (x5 : Original.LF_DOT_IndProp.LF.IndProp.reg_exp Ascii.ascii) (x6 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp imported_Ascii_ascii)
    (hx1 : rel_iso (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso Ascii_ascii_iso) x5 x6),
  rel_iso
    (relax_Iso_Ts_Ps
       (iff_iso (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso hx (Original_LF__DOT__IndProp_LF_IndProp_App_iso hx0 hx1))
          (ex_iso
             (fun s0 : Original.LF_DOT_Poly.LF.Poly.list Ascii.ascii =>
              exists s1 : Original.LF_DOT_Poly.LF.Poly.list Ascii.ascii,
                x1 = Original.LF_DOT_Poly.LF.Poly.app s0 s1 /\ Original.LF_DOT_IndProp.LF.IndProp.exp_match s0 x3 /\ Original.LF_DOT_IndProp.LF.IndProp.exp_match s1 x5)
             (fun H : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii =>
              imported_ex
                (fun H0 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii =>
                 imported_and (imported_Corelib_Init_Logic_eq x2 (imported_Original_LF__DOT__Poly_LF_Poly_app H H0))
                   (imported_and (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match H x4) (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match H0 x6))))
             (fun (x7 : Original.LF_DOT_Poly.LF.Poly.list Ascii.ascii) (x8 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii)
                (hx2 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso Ascii_ascii_iso) x7 x8) =>
              ex_iso
                (fun s1 : Original.LF_DOT_Poly.LF.Poly.list Ascii.ascii =>
                 x1 = Original.LF_DOT_Poly.LF.Poly.app x7 s1 /\ Original.LF_DOT_IndProp.LF.IndProp.exp_match x7 x3 /\ Original.LF_DOT_IndProp.LF.IndProp.exp_match s1 x5)
                (fun H : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii =>
                 imported_and (imported_Corelib_Init_Logic_eq x2 (imported_Original_LF__DOT__Poly_LF_Poly_app x8 H))
                   (imported_and (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match x8 x4) (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match H x6)))
                (fun (x9 : Original.LF_DOT_Poly.LF.Poly.list Ascii.ascii) (x10 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii)
                   (hx3 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso Ascii_ascii_iso) x9 x10) =>
                 and_iso (Corelib_Init_Logic_eq_iso hx (Original_LF__DOT__Poly_LF_Poly_app_iso hx2 hx3))
                   (and_iso (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso hx2 hx0) (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso hx3 hx1)))))))
    (Original.LF_DOT_IndProp.LF.IndProp.app_exists x1 x3 x5) (imported_Original_LF__DOT__IndProp_LF_IndProp_app__exists x2 x4 x6).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_app__exists_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.app_exists ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_app__exists_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.app_exists imported_Original_LF__DOT__IndProp_LF_IndProp_app__exists ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_app__exists_iso; constructor : typeclass_instances.


End Interface.