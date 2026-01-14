From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_altU_auto__U2_lf__U_altU_auto__nonzeros__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_altU_auto__U2_lf__U_altU_auto__nonzeros__iso.

  Export Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_altU_auto__U2_lf__U_altU_auto__nonzeros__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_altU_auto__U2_lf__U_altU_auto__nonzeros__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__AltAuto_LF_AltAuto_nonzeros__app : forall x x0 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat,
  imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__AltAuto_LF_AltAuto_nonzeros (imported_Original_LF__DOT__Poly_LF_Poly_app x x0))
    (imported_Original_LF__DOT__Poly_LF_Poly_app (imported_Original_LF__DOT__AltAuto_LF_AltAuto_nonzeros x) (imported_Original_LF__DOT__AltAuto_LF_AltAuto_nonzeros x0)).
Parameter Original_LF__DOT__AltAuto_LF_AltAuto_nonzeros__app_iso : forall (x1 : Original.LF_DOT_Poly.LF.Poly.list nat) (x2 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat) (hx : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso nat_iso) x1 x2)
    (x3 : Original.LF_DOT_Poly.LF.Poly.list nat) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat) (hx0 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso nat_iso) x3 x4),
  rel_iso
    (Corelib_Init_Logic_eq_iso (Original_LF__DOT__AltAuto_LF_AltAuto_nonzeros_iso (Original_LF__DOT__Poly_LF_Poly_app_iso hx hx0))
       (Original_LF__DOT__Poly_LF_Poly_app_iso (Original_LF__DOT__AltAuto_LF_AltAuto_nonzeros_iso hx) (Original_LF__DOT__AltAuto_LF_AltAuto_nonzeros_iso hx0)))
    (Original.LF_DOT_AltAuto.LF.AltAuto.nonzeros_app x1 x3) (imported_Original_LF__DOT__AltAuto_LF_AltAuto_nonzeros__app x2 x4).
Existing Instance Original_LF__DOT__AltAuto_LF_AltAuto_nonzeros__app_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.nonzeros_app ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_nonzeros__app_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.nonzeros_app imported_Original_LF__DOT__AltAuto_LF_AltAuto_nonzeros__app ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_nonzeros__app_iso; constructor : typeclass_instances.


End Interface.