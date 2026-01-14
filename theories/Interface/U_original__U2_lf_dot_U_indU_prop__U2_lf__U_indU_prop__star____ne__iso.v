From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_star__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.and__iso Interface.ex__iso Interface.iff__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_star__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.and__iso Interface.ex__iso Interface.iff__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_star__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.and__iso.CodeBlocks Interface.ex__iso.CodeBlocks Interface.iff__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_star__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.and__iso.Interface <+ Interface.ex__iso.Interface <+ Interface.iff__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_star__ne : forall (x : imported_Ascii_ascii) (x0 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii) (x1 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp imported_Ascii_ascii),
  imported_iff (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match (imported_Original_LF__DOT__Poly_LF_Poly_cons x x0) (imported_Original_LF__DOT__IndProp_LF_IndProp_Star x1))
    (imported_ex
       (fun H : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii =>
        imported_ex
          (fun H0 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii =>
           imported_and (imported_Corelib_Init_Logic_eq x0 (imported_Original_LF__DOT__Poly_LF_Poly_app H H0))
             (imported_and (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match (imported_Original_LF__DOT__Poly_LF_Poly_cons x H) x1)
                (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match H0 (imported_Original_LF__DOT__IndProp_LF_IndProp_Star x1)))))).
Parameter Original_LF__DOT__IndProp_LF_IndProp_star__ne_iso : forall (x1 : Ascii.ascii) (x2 : imported_Ascii_ascii) (hx : rel_iso Ascii_ascii_iso x1 x2) (x3 : Original.LF_DOT_Poly.LF.Poly.list Ascii.ascii)
    (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii) (hx0 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso Ascii_ascii_iso) x3 x4)
    (x5 : Original.LF_DOT_IndProp.LF.IndProp.reg_exp Ascii.ascii) (x6 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp imported_Ascii_ascii)
    (hx1 : rel_iso (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso Ascii_ascii_iso) x5 x6),
  rel_iso
    {|
      to :=
        iff_iso (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso hx hx0) (Original_LF__DOT__IndProp_LF_IndProp_Star_iso hx1))
          (ex_iso
             (fun s0 : Original.LF_DOT_Poly.LF.Poly.list Ascii.ascii =>
              exists s1 : Original.LF_DOT_Poly.LF.Poly.list Ascii.ascii,
                x3 = Original.LF_DOT_Poly.LF.Poly.app s0 s1 /\
                Original.LF_DOT_IndProp.LF.IndProp.exp_match (Original.LF_DOT_Poly.LF.Poly.cons x1 s0) x5 /\
                Original.LF_DOT_IndProp.LF.IndProp.exp_match s1 (Original.LF_DOT_IndProp.LF.IndProp.Star x5))
             (fun H : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii =>
              imported_ex
                (fun H0 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii =>
                 imported_and (imported_Corelib_Init_Logic_eq x4 (imported_Original_LF__DOT__Poly_LF_Poly_app H H0))
                   (imported_and (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match (imported_Original_LF__DOT__Poly_LF_Poly_cons x2 H) x6)
                      (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match H0 (imported_Original_LF__DOT__IndProp_LF_IndProp_Star x6)))))
             (fun (x7 : Original.LF_DOT_Poly.LF.Poly.list Ascii.ascii) (x8 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii)
                (hx2 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso Ascii_ascii_iso) x7 x8) =>
              ex_iso
                (fun s1 : Original.LF_DOT_Poly.LF.Poly.list Ascii.ascii =>
                 x3 = Original.LF_DOT_Poly.LF.Poly.app x7 s1 /\
                 Original.LF_DOT_IndProp.LF.IndProp.exp_match (Original.LF_DOT_Poly.LF.Poly.cons x1 x7) x5 /\
                 Original.LF_DOT_IndProp.LF.IndProp.exp_match s1 (Original.LF_DOT_IndProp.LF.IndProp.Star x5))
                (fun H : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii =>
                 imported_and (imported_Corelib_Init_Logic_eq x4 (imported_Original_LF__DOT__Poly_LF_Poly_app x8 H))
                   (imported_and (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match (imported_Original_LF__DOT__Poly_LF_Poly_cons x2 x8) x6)
                      (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match H (imported_Original_LF__DOT__IndProp_LF_IndProp_Star x6))))
                (fun (x9 : Original.LF_DOT_Poly.LF.Poly.list Ascii.ascii) (x10 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii)
                   (hx3 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso Ascii_ascii_iso) x9 x10) =>
                 and_iso (Corelib_Init_Logic_eq_iso hx0 (Original_LF__DOT__Poly_LF_Poly_app_iso hx2 hx3))
                   (and_iso (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso hx hx2) hx1)
                      (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso hx3 (Original_LF__DOT__IndProp_LF_IndProp_Star_iso hx1))))));
      from :=
        from
          (iff_iso (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso hx hx0) (Original_LF__DOT__IndProp_LF_IndProp_Star_iso hx1))
             (ex_iso
                (fun s0 : Original.LF_DOT_Poly.LF.Poly.list Ascii.ascii =>
                 exists s1 : Original.LF_DOT_Poly.LF.Poly.list Ascii.ascii,
                   x3 = Original.LF_DOT_Poly.LF.Poly.app s0 s1 /\
                   Original.LF_DOT_IndProp.LF.IndProp.exp_match (Original.LF_DOT_Poly.LF.Poly.cons x1 s0) x5 /\
                   Original.LF_DOT_IndProp.LF.IndProp.exp_match s1 (Original.LF_DOT_IndProp.LF.IndProp.Star x5))
                (fun H : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii =>
                 imported_ex
                   (fun H0 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii =>
                    imported_and (imported_Corelib_Init_Logic_eq x4 (imported_Original_LF__DOT__Poly_LF_Poly_app H H0))
                      (imported_and (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match (imported_Original_LF__DOT__Poly_LF_Poly_cons x2 H) x6)
                         (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match H0 (imported_Original_LF__DOT__IndProp_LF_IndProp_Star x6)))))
                (fun (x7 : Original.LF_DOT_Poly.LF.Poly.list Ascii.ascii) (x8 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii)
                   (hx2 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso Ascii_ascii_iso) x7 x8) =>
                 ex_iso
                   (fun s1 : Original.LF_DOT_Poly.LF.Poly.list Ascii.ascii =>
                    x3 = Original.LF_DOT_Poly.LF.Poly.app x7 s1 /\
                    Original.LF_DOT_IndProp.LF.IndProp.exp_match (Original.LF_DOT_Poly.LF.Poly.cons x1 x7) x5 /\
                    Original.LF_DOT_IndProp.LF.IndProp.exp_match s1 (Original.LF_DOT_IndProp.LF.IndProp.Star x5))
                   (fun H : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii =>
                    imported_and (imported_Corelib_Init_Logic_eq x4 (imported_Original_LF__DOT__Poly_LF_Poly_app x8 H))
                      (imported_and (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match (imported_Original_LF__DOT__Poly_LF_Poly_cons x2 x8) x6)
                         (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match H (imported_Original_LF__DOT__IndProp_LF_IndProp_Star x6))))
                   (fun (x9 : Original.LF_DOT_Poly.LF.Poly.list Ascii.ascii) (x10 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii)
                      (hx3 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso Ascii_ascii_iso) x9 x10) =>
                    and_iso (Corelib_Init_Logic_eq_iso hx0 (Original_LF__DOT__Poly_LF_Poly_app_iso hx2 hx3))
                      (and_iso (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso hx hx2) hx1)
                         (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso hx3 (Original_LF__DOT__IndProp_LF_IndProp_Star_iso hx1)))))));
      to_from :=
        fun
          x : imported_iff (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match (imported_Original_LF__DOT__Poly_LF_Poly_cons x2 x4) (imported_Original_LF__DOT__IndProp_LF_IndProp_Star x6))
                (imported_ex
                   (fun H : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii =>
                    imported_ex
                      (fun H0 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii =>
                       imported_and (imported_Corelib_Init_Logic_eq x4 (imported_Original_LF__DOT__Poly_LF_Poly_app H H0))
                         (imported_and (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match (imported_Original_LF__DOT__Poly_LF_Poly_cons x2 H) x6)
                            (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match H0 (imported_Original_LF__DOT__IndProp_LF_IndProp_Star x6)))))) =>
        to_from
          (iff_iso (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso hx hx0) (Original_LF__DOT__IndProp_LF_IndProp_Star_iso hx1))
             (ex_iso
                (fun s0 : Original.LF_DOT_Poly.LF.Poly.list Ascii.ascii =>
                 exists s1 : Original.LF_DOT_Poly.LF.Poly.list Ascii.ascii,
                   x3 = Original.LF_DOT_Poly.LF.Poly.app s0 s1 /\
                   Original.LF_DOT_IndProp.LF.IndProp.exp_match (Original.LF_DOT_Poly.LF.Poly.cons x1 s0) x5 /\
                   Original.LF_DOT_IndProp.LF.IndProp.exp_match s1 (Original.LF_DOT_IndProp.LF.IndProp.Star x5))
                (fun H : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii =>
                 imported_ex
                   (fun H0 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii =>
                    imported_and (imported_Corelib_Init_Logic_eq x4 (imported_Original_LF__DOT__Poly_LF_Poly_app H H0))
                      (imported_and (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match (imported_Original_LF__DOT__Poly_LF_Poly_cons x2 H) x6)
                         (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match H0 (imported_Original_LF__DOT__IndProp_LF_IndProp_Star x6)))))
                (fun (x7 : Original.LF_DOT_Poly.LF.Poly.list Ascii.ascii) (x8 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii)
                   (hx2 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso Ascii_ascii_iso) x7 x8) =>
                 ex_iso
                   (fun s1 : Original.LF_DOT_Poly.LF.Poly.list Ascii.ascii =>
                    x3 = Original.LF_DOT_Poly.LF.Poly.app x7 s1 /\
                    Original.LF_DOT_IndProp.LF.IndProp.exp_match (Original.LF_DOT_Poly.LF.Poly.cons x1 x7) x5 /\
                    Original.LF_DOT_IndProp.LF.IndProp.exp_match s1 (Original.LF_DOT_IndProp.LF.IndProp.Star x5))
                   (fun H : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii =>
                    imported_and (imported_Corelib_Init_Logic_eq x4 (imported_Original_LF__DOT__Poly_LF_Poly_app x8 H))
                      (imported_and (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match (imported_Original_LF__DOT__Poly_LF_Poly_cons x2 x8) x6)
                         (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match H (imported_Original_LF__DOT__IndProp_LF_IndProp_Star x6))))
                   (fun (x9 : Original.LF_DOT_Poly.LF.Poly.list Ascii.ascii) (x10 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii)
                      (hx3 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso Ascii_ascii_iso) x9 x10) =>
                    and_iso (Corelib_Init_Logic_eq_iso hx0 (Original_LF__DOT__Poly_LF_Poly_app_iso hx2 hx3))
                      (and_iso (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso hx hx2) hx1)
                         (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso hx3 (Original_LF__DOT__IndProp_LF_IndProp_Star_iso hx1)))))))
          x;
      from_to :=
        fun
          x : Original.LF_DOT_IndProp.LF.IndProp.exp_match (Original.LF_DOT_Poly.LF.Poly.cons x1 x3) (Original.LF_DOT_IndProp.LF.IndProp.Star x5) <->
              (exists s0 s1 : Original.LF_DOT_Poly.LF.Poly.list Ascii.ascii,
                 x3 = Original.LF_DOT_Poly.LF.Poly.app s0 s1 /\
                 Original.LF_DOT_IndProp.LF.IndProp.exp_match (Original.LF_DOT_Poly.LF.Poly.cons x1 s0) x5 /\
                 Original.LF_DOT_IndProp.LF.IndProp.exp_match s1 (Original.LF_DOT_IndProp.LF.IndProp.Star x5)) =>
        seq_p_of_t
          (from_to
             (iff_iso (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso hx hx0) (Original_LF__DOT__IndProp_LF_IndProp_Star_iso hx1))
                (ex_iso
                   (fun s0 : Original.LF_DOT_Poly.LF.Poly.list Ascii.ascii =>
                    exists s1 : Original.LF_DOT_Poly.LF.Poly.list Ascii.ascii,
                      x3 = Original.LF_DOT_Poly.LF.Poly.app s0 s1 /\
                      Original.LF_DOT_IndProp.LF.IndProp.exp_match (Original.LF_DOT_Poly.LF.Poly.cons x1 s0) x5 /\
                      Original.LF_DOT_IndProp.LF.IndProp.exp_match s1 (Original.LF_DOT_IndProp.LF.IndProp.Star x5))
                   (fun H : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii =>
                    imported_ex
                      (fun H0 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii =>
                       imported_and (imported_Corelib_Init_Logic_eq x4 (imported_Original_LF__DOT__Poly_LF_Poly_app H H0))
                         (imported_and (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match (imported_Original_LF__DOT__Poly_LF_Poly_cons x2 H) x6)
                            (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match H0 (imported_Original_LF__DOT__IndProp_LF_IndProp_Star x6)))))
                   (fun (x7 : Original.LF_DOT_Poly.LF.Poly.list Ascii.ascii) (x8 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii)
                      (hx2 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso Ascii_ascii_iso) x7 x8) =>
                    ex_iso
                      (fun s1 : Original.LF_DOT_Poly.LF.Poly.list Ascii.ascii =>
                       x3 = Original.LF_DOT_Poly.LF.Poly.app x7 s1 /\
                       Original.LF_DOT_IndProp.LF.IndProp.exp_match (Original.LF_DOT_Poly.LF.Poly.cons x1 x7) x5 /\
                       Original.LF_DOT_IndProp.LF.IndProp.exp_match s1 (Original.LF_DOT_IndProp.LF.IndProp.Star x5))
                      (fun H : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii =>
                       imported_and (imported_Corelib_Init_Logic_eq x4 (imported_Original_LF__DOT__Poly_LF_Poly_app x8 H))
                         (imported_and (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match (imported_Original_LF__DOT__Poly_LF_Poly_cons x2 x8) x6)
                            (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match H (imported_Original_LF__DOT__IndProp_LF_IndProp_Star x6))))
                      (fun (x9 : Original.LF_DOT_Poly.LF.Poly.list Ascii.ascii) (x10 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii)
                         (hx3 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso Ascii_ascii_iso) x9 x10) =>
                       and_iso (Corelib_Init_Logic_eq_iso hx0 (Original_LF__DOT__Poly_LF_Poly_app_iso hx2 hx3))
                         (and_iso (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso hx hx2) hx1)
                            (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso hx3 (Original_LF__DOT__IndProp_LF_IndProp_Star_iso hx1)))))))
             x)
    |} (Original.LF_DOT_IndProp.LF.IndProp.star_ne x1 x3 x5) (imported_Original_LF__DOT__IndProp_LF_IndProp_star__ne x2 x4 x6).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_star__ne_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.star_ne ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_star__ne_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.star_ne imported_Original_LF__DOT__IndProp_LF_IndProp_star__ne ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_star__ne_iso; constructor : typeclass_instances.


End Interface.