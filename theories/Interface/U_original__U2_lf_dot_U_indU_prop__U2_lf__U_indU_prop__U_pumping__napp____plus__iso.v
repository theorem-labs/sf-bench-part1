From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_nat__add__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_pumping__napp__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_nat__add__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_pumping__napp__iso.

  Export Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_nat__add__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_pumping__napp__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_nat__add__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_pumping__napp__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_Pumping_napp__plus : forall (x : Type) (x0 x1 : imported_nat) (x2 : imported_Original_LF__DOT__Poly_LF_Poly_list x),
  imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__IndProp_LF_IndProp_Pumping_napp (imported_Nat_add x0 x1) x2)
    (imported_Original_LF__DOT__Poly_LF_Poly_app (imported_Original_LF__DOT__IndProp_LF_IndProp_Pumping_napp x0 x2) (imported_Original_LF__DOT__IndProp_LF_IndProp_Pumping_napp x1 x2)).
Parameter Original_LF__DOT__IndProp_LF_IndProp_Pumping_napp__plus_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) (x5 : nat) (x6 : imported_nat) (hx1 : rel_iso nat_iso x5 x6)
    (x7 : Original.LF_DOT_Poly.LF.Poly.list x1) (x8 : imported_Original_LF__DOT__Poly_LF_Poly_list x2) (hx2 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x7 x8),
  rel_iso
    (Corelib_Init_Logic_eq_iso (Original_LF__DOT__IndProp_LF_IndProp_Pumping_napp_iso (Nat_add_iso hx0 hx1) hx2)
       (Original_LF__DOT__Poly_LF_Poly_app_iso (Original_LF__DOT__IndProp_LF_IndProp_Pumping_napp_iso hx0 hx2) (Original_LF__DOT__IndProp_LF_IndProp_Pumping_napp_iso hx1 hx2)))
    (Original.LF_DOT_IndProp.LF.IndProp.Pumping.napp_plus x1 x3 x5 x7) (imported_Original_LF__DOT__IndProp_LF_IndProp_Pumping_napp__plus x4 x6 x8).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_Pumping_napp__plus_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.Pumping.napp_plus ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_Pumping_napp__plus_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.Pumping.napp_plus imported_Original_LF__DOT__IndProp_LF_IndProp_Pumping_napp__plus ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_Pumping_napp__plus_iso; constructor : typeclass_instances.


End Interface.