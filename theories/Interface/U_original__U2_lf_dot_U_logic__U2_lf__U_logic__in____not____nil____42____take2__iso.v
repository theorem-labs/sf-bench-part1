From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_false__iso Interface.U_logic__not__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_s__iso Interface.__0__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_false__iso Interface.U_logic__not__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_s__iso Interface.__0__iso.

  Export Interface.U_false__iso.CodeBlocks Interface.U_logic__not__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_false__iso.Interface <+ Interface.U_logic__not__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_in__not__nil__42__take2 : forall x : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat,
  imported_Original_LF__DOT__Logic_LF_Logic_In (imported_S (imported_S (imported_S (iterate1 imported_S 39 imported_0)))) x ->
  imported_Corelib_Init_Logic_eq x (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat) -> imported_False.
Parameter Original_LF__DOT__Logic_LF_Logic_in__not__nil__42__take2_iso : forall (x1 : Original.LF_DOT_Poly.LF.Poly.list nat) (x2 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat) (hx : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso nat_iso) x1 x2)
    (x3 : Original.LF_DOT_Logic.LF.Logic.In 42 x1) (x4 : imported_Original_LF__DOT__Logic_LF_Logic_In (imported_S (imported_S (imported_S (iterate1 imported_S 39 imported_0)))) x2),
  rel_iso (Original_LF__DOT__Logic_LF_Logic_In_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 39 0 imported_0 _0_iso)))) hx) x3 x4 ->
  forall (x5 : x1 = Original.LF_DOT_Poly.LF.Poly.nil) (x6 : imported_Corelib_Init_Logic_eq x2 (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat)),
  rel_iso (Corelib_Init_Logic_eq_iso hx (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)) x5 x6 ->
  rel_iso False_iso (Original.LF_DOT_Logic.LF.Logic.in_not_nil_42_take2 x1 x3 x5) (imported_Original_LF__DOT__Logic_LF_Logic_in__not__nil__42__take2 x4 x6).
Existing Instance Original_LF__DOT__Logic_LF_Logic_in__not__nil__42__take2_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.in_not_nil_42_take2 ?x) => unify x Original_LF__DOT__Logic_LF_Logic_in__not__nil__42__take2_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.in_not_nil_42_take2 imported_Original_LF__DOT__Logic_LF_Logic_in__not__nil__42__take2 ?x) => unify x Original_LF__DOT__Logic_LF_Logic_in__not__nil__42__take2_iso; constructor : typeclass_instances.


End Interface.