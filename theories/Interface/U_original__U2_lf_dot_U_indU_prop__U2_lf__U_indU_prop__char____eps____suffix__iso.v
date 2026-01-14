From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_char__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.iff__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_char__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.iff__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_char__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.iff__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_char__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.iff__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_char__eps__suffix : forall (x : imported_Ascii_ascii) (x0 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii),
  imported_iff (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match (imported_Original_LF__DOT__Poly_LF_Poly_cons x x0) (imported_Original_LF__DOT__IndProp_LF_IndProp_Char x))
    (imported_Corelib_Init_Logic_eq x0 (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_Ascii_ascii)).
Parameter Original_LF__DOT__IndProp_LF_IndProp_char__eps__suffix_iso : forall (x1 : Ascii.ascii) (x2 : imported_Ascii_ascii) (hx : rel_iso Ascii_ascii_iso x1 x2) (x3 : Original.LF_DOT_Poly.LF.Poly.list Ascii.ascii)
    (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii) (hx0 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso Ascii_ascii_iso) x3 x4),
  rel_iso
    {|
      to :=
        iff_iso (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso hx hx0) (Original_LF__DOT__IndProp_LF_IndProp_Char_iso hx))
          (Corelib_Init_Logic_eq_iso hx0 (Original_LF__DOT__Poly_LF_Poly_nil_iso Ascii_ascii_iso));
      from :=
        from
          (iff_iso (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso hx hx0) (Original_LF__DOT__IndProp_LF_IndProp_Char_iso hx))
             (Corelib_Init_Logic_eq_iso hx0 (Original_LF__DOT__Poly_LF_Poly_nil_iso Ascii_ascii_iso)));
      to_from :=
        fun
          x : imported_iff (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match (imported_Original_LF__DOT__Poly_LF_Poly_cons x2 x4) (imported_Original_LF__DOT__IndProp_LF_IndProp_Char x2))
                (imported_Corelib_Init_Logic_eq x4 (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_Ascii_ascii)) =>
        to_from
          (iff_iso (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso hx hx0) (Original_LF__DOT__IndProp_LF_IndProp_Char_iso hx))
             (Corelib_Init_Logic_eq_iso hx0 (Original_LF__DOT__Poly_LF_Poly_nil_iso Ascii_ascii_iso)))
          x;
      from_to :=
        fun x : Original.LF_DOT_IndProp.LF.IndProp.exp_match (Original.LF_DOT_Poly.LF.Poly.cons x1 x3) (Original.LF_DOT_IndProp.LF.IndProp.Char x1) <-> x3 = Original.LF_DOT_Poly.LF.Poly.nil =>
        seq_p_of_t
          (from_to
             (iff_iso (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso hx hx0) (Original_LF__DOT__IndProp_LF_IndProp_Char_iso hx))
                (Corelib_Init_Logic_eq_iso hx0 (Original_LF__DOT__Poly_LF_Poly_nil_iso Ascii_ascii_iso)))
             x)
    |} (Original.LF_DOT_IndProp.LF.IndProp.char_eps_suffix x1 x3) (imported_Original_LF__DOT__IndProp_LF_IndProp_char__eps__suffix x2 x4).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_char__eps__suffix_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.char_eps_suffix ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_char__eps__suffix_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.char_eps_suffix imported_Original_LF__DOT__IndProp_LF_IndProp_char__eps__suffix ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_char__eps__suffix_iso; constructor : typeclass_instances.


End Interface.