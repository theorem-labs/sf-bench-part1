From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.U_false__iso Interface.U_logic__not__iso Interface.U_original__U_false__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_char__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.iff__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.U_false__iso Interface.U_logic__not__iso Interface.U_original__U_false__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_char__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.iff__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.U_false__iso.CodeBlocks Interface.U_logic__not__iso.CodeBlocks Interface.U_original__U_false__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_char__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.iff__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.U_false__iso.Interface <+ Interface.U_logic__not__iso.Interface <+ Interface.U_original__U_false__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_char__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.iff__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_char__nomatch__char : forall (x x0 : imported_Ascii_ascii) (x1 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii),
  (imported_Corelib_Init_Logic_eq x0 x -> imported_False) ->
  imported_iff (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match (imported_Original_LF__DOT__Poly_LF_Poly_cons x0 x1) (imported_Original_LF__DOT__IndProp_LF_IndProp_Char x))
    imported_Original_False.
Parameter Original_LF__DOT__IndProp_LF_IndProp_char__nomatch__char_iso : forall (x1 : Ascii.ascii) (x2 : imported_Ascii_ascii) (hx : rel_iso Ascii_ascii_iso x1 x2) (x3 : Ascii.ascii) (x4 : imported_Ascii_ascii) (hx0 : rel_iso Ascii_ascii_iso x3 x4)
    (x5 : Original.LF_DOT_Poly.LF.Poly.list Ascii.ascii) (x6 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii)
    (hx1 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso Ascii_ascii_iso) x5 x6) (x7 : x3 <> x1) (x8 : imported_Corelib_Init_Logic_eq x4 x2 -> imported_False),
  (forall (x9 : x3 = x1) (x10 : imported_Corelib_Init_Logic_eq x4 x2), rel_iso (relax_Iso_Ts_Ps (Corelib_Init_Logic_eq_iso hx0 hx)) x9 x10 -> rel_iso (relax_Iso_Ts_Ps False_iso) (x7 x9) (x8 x10)) ->
  rel_iso
    (relax_Iso_Ts_Ps
       (iff_iso (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso hx0 hx1) (Original_LF__DOT__IndProp_LF_IndProp_Char_iso hx)) Original_False_iso))
    (Original.LF_DOT_IndProp.LF.IndProp.char_nomatch_char x1 x3 x5 x7) (imported_Original_LF__DOT__IndProp_LF_IndProp_char__nomatch__char x6 x8).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_char__nomatch__char_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.char_nomatch_char ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_char__nomatch__char_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.char_nomatch_char imported_Original_LF__DOT__IndProp_LF_IndProp_char__nomatch__char ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_char__nomatch__char_iso; constructor : typeclass_instances.


End Interface.