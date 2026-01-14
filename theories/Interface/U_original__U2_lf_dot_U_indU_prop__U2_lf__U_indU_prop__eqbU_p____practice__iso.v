From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_false__iso Interface.U_logic__not__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__count__iso Interface.__0__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_false__iso Interface.U_logic__not__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__count__iso Interface.__0__iso.

  Export Interface.U_false__iso.CodeBlocks Interface.U_logic__not__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__count__iso.CodeBlocks Interface.__0__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_false__iso.Interface <+ Interface.U_logic__not__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__count__iso.Interface <+ Interface.__0__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_eqbP__practice : forall (x : imported_nat) (x0 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat),
  imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__IndProp_LF_IndProp_count x x0) imported_0 -> imported_Original_LF__DOT__Logic_LF_Logic_In x x0 -> imported_False.
Parameter Original_LF__DOT__IndProp_LF_IndProp_eqbP__practice_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : Original.LF_DOT_Poly.LF.Poly.list nat) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat)
    (hx0 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso nat_iso) x3 x4) (x5 : Original.LF_DOT_IndProp.LF.IndProp.count x1 x3 = 0)
    (x6 : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__IndProp_LF_IndProp_count x2 x4) imported_0),
  rel_iso (Corelib_Init_Logic_eq_iso (Original_LF__DOT__IndProp_LF_IndProp_count_iso hx hx0) _0_iso) x5 x6 ->
  forall (x7 : Original.LF_DOT_Logic.LF.Logic.In x1 x3) (x8 : imported_Original_LF__DOT__Logic_LF_Logic_In x2 x4),
  rel_iso (Original_LF__DOT__Logic_LF_Logic_In_iso hx hx0) x7 x8 ->
  rel_iso False_iso (Original.LF_DOT_IndProp.LF.IndProp.eqbP_practice x1 x3 x5 x7) (imported_Original_LF__DOT__IndProp_LF_IndProp_eqbP__practice x6 x8).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_eqbP__practice_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.eqbP_practice ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_eqbP__practice_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.eqbP_practice imported_Original_LF__DOT__IndProp_LF_IndProp_eqbP__practice ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_eqbP__practice_iso; constructor : typeclass_instances.


End Interface.