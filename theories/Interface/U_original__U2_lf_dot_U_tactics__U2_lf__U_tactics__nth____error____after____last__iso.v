From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__option__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_none__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__length__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nth____error__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__option__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_none__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__length__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nth____error__iso.

  Export Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__option__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_none__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__length__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nth____error__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__option__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_none__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__length__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nth____error__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Tactics_LF_Tactics_nth__error__after__last : forall (x : imported_nat) (x0 : Type) (x1 : imported_Original_LF__DOT__Poly_LF_Poly_list x0),
  imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Poly_LF_Poly_length x1) x ->
  imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Poly_LF_Poly_nth__error x1 x) (imported_Original_LF__DOT__Poly_LF_Poly_None x0).
Parameter Original_LF__DOT__Tactics_LF_Tactics_nth__error__after__last_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 x4 : Type) (hx0 : Iso x3 x4) (x5 : Original.LF_DOT_Poly.LF.Poly.list x3)
    (x6 : imported_Original_LF__DOT__Poly_LF_Poly_list x4) (hx1 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx0) x5 x6) (x7 : Original.LF_DOT_Poly.LF.Poly.length x5 = x1)
    (x8 : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Poly_LF_Poly_length x6) x2),
  rel_iso (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Poly_LF_Poly_length_iso hx1) hx) x7 x8 ->
  rel_iso (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Poly_LF_Poly_nth__error_iso hx1 hx) (Original_LF__DOT__Poly_LF_Poly_None_iso hx0))
    (Original.LF_DOT_Tactics.LF.Tactics.nth_error_after_last x1 x3 x5 x7) (imported_Original_LF__DOT__Tactics_LF_Tactics_nth__error__after__last x8).
Existing Instance Original_LF__DOT__Tactics_LF_Tactics_nth__error__after__last_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Tactics.LF.Tactics.nth_error_after_last ?x) => unify x Original_LF__DOT__Tactics_LF_Tactics_nth__error__after__last_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Tactics.LF.Tactics.nth_error_after_last imported_Original_LF__DOT__Tactics_LF_Tactics_nth__error__after__last ?x) => unify x Original_LF__DOT__Tactics_LF_Tactics_nth__error__after__last_iso; constructor : typeclass_instances.


End Interface.