From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__pal__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__rev__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__pal__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__rev__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso.

  Export Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__pal__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__rev__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__pal__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__rev__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_palindrome__converse : forall (x : Type) (x0 : imported_Original_LF__DOT__Poly_LF_Poly_list x),
  imported_Corelib_Init_Logic_eq x0 (imported_Original_LF__DOT__Poly_LF_Poly_rev x0) -> imported_Original_LF__DOT__IndProp_LF_IndProp_pal x0.
Parameter Original_LF__DOT__IndProp_LF_IndProp_palindrome__converse_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_Poly.LF.Poly.list x1) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2)
    (hx0 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x3 x4) (x5 : x3 = Original.LF_DOT_Poly.LF.Poly.rev x3)
    (x6 : imported_Corelib_Init_Logic_eq x4 (imported_Original_LF__DOT__Poly_LF_Poly_rev x4)),
  rel_iso (Corelib_Init_Logic_eq_iso hx0 (Original_LF__DOT__Poly_LF_Poly_rev_iso hx0)) x5 x6 ->
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_pal_iso hx0) (Original.LF_DOT_IndProp.LF.IndProp.palindrome_converse x3 x5) (imported_Original_LF__DOT__IndProp_LF_IndProp_palindrome__converse x6).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_palindrome__converse_iso.
#[export] Hint Extern 0 (IsoStatementProofFor (@Original.LF_DOT_IndProp.LF.IndProp.palindrome_converse) ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_palindrome__converse_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween (@Original.LF_DOT_IndProp.LF.IndProp.palindrome_converse) imported_Original_LF__DOT__IndProp_LF_IndProp_palindrome__converse ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_palindrome__converse_iso; constructor : typeclass_instances.


End Interface.