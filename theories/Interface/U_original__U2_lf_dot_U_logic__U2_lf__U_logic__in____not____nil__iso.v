From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_false__iso Interface.U_logic__not__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_false__iso Interface.U_logic__not__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso.

  Export Interface.U_false__iso.CodeBlocks Interface.U_logic__not__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_false__iso.Interface <+ Interface.U_logic__not__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_in__not__nil : forall (x : Type) (x0 : x) (x1 : imported_Original_LF__DOT__Poly_LF_Poly_list x),
  imported_Original_LF__DOT__Logic_LF_Logic_In x0 x1 -> imported_Corelib_Init_Logic_eq x1 (imported_Original_LF__DOT__Poly_LF_Poly_nil x) -> imported_False.
Parameter Original_LF__DOT__Logic_LF_Logic_in__not__nil_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (hx0 : rel_iso hx x3 x4) (x5 : Original.LF_DOT_Poly.LF.Poly.list x1) (x6 : imported_Original_LF__DOT__Poly_LF_Poly_list x2)
    (hx1 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x5 x6) (x7 : Original.LF_DOT_Logic.LF.Logic.In x3 x5) (x8 : imported_Original_LF__DOT__Logic_LF_Logic_In x4 x6),
  rel_iso (Original_LF__DOT__Logic_LF_Logic_In_iso hx0 hx1) x7 x8 ->
  forall (x9 : x5 = Original.LF_DOT_Poly.LF.Poly.nil) (x10 : imported_Corelib_Init_Logic_eq x6 (imported_Original_LF__DOT__Poly_LF_Poly_nil x2)),
  rel_iso (Corelib_Init_Logic_eq_iso hx1 (Original_LF__DOT__Poly_LF_Poly_nil_iso hx)) x9 x10 ->
  rel_iso False_iso (Original.LF_DOT_Logic.LF.Logic.in_not_nil x1 x3 x5 x7 x9) (imported_Original_LF__DOT__Logic_LF_Logic_in__not__nil x8 x10).
Existing Instance Original_LF__DOT__Logic_LF_Logic_in__not__nil_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.in_not_nil ?x) => unify x Original_LF__DOT__Logic_LF_Logic_in__not__nil_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.in_not_nil imported_Original_LF__DOT__Logic_LF_Logic_in__not__nil ?x) => unify x Original_LF__DOT__Logic_LF_Logic_in__not__nil_iso; constructor : typeclass_instances.


End Interface.