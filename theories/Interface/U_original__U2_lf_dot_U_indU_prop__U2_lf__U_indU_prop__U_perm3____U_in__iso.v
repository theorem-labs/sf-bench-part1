From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_perm3U_reminder__U_perm3__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_perm3U_reminder__U_perm3__iso Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso.

  Export Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_perm3U_reminder__U_perm3__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_perm3U_reminder__U_perm3__iso.Interface <+ Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_Perm3__In : forall (x : Type) (x0 : x) (x1 x2 : imported_Original_LF__DOT__Poly_LF_Poly_list x),
  imported_Original_LF__DOT__IndProp_LF_IndProp_Perm3Reminder_Perm3 x1 x2 -> imported_Original_LF__DOT__Logic_LF_Logic_In x0 x1 -> imported_Original_LF__DOT__Logic_LF_Logic_In x0 x2.
Parameter Original_LF__DOT__IndProp_LF_IndProp_Perm3__In_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (hx0 : rel_iso hx x3 x4) (x5 : Original.LF_DOT_Poly.LF.Poly.list x1) (x6 : imported_Original_LF__DOT__Poly_LF_Poly_list x2)
    (hx1 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x5 x6) (x7 : Original.LF_DOT_Poly.LF.Poly.list x1) (x8 : imported_Original_LF__DOT__Poly_LF_Poly_list x2)
    (hx2 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x7 x8) (x9 : Original.LF_DOT_IndProp.LF.IndProp.Perm3Reminder.Perm3 x5 x7)
    (x10 : imported_Original_LF__DOT__IndProp_LF_IndProp_Perm3Reminder_Perm3 x6 x8),
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_Perm3Reminder_Perm3_iso hx1 hx2) x9 x10 ->
  forall (x11 : Original.LF_DOT_Logic.LF.Logic.In x3 x5) (x12 : imported_Original_LF__DOT__Logic_LF_Logic_In x4 x6),
  rel_iso (Original_LF__DOT__Logic_LF_Logic_In_iso hx0 hx1) x11 x12 ->
  rel_iso (Original_LF__DOT__Logic_LF_Logic_In_iso hx0 hx2) (Original.LF_DOT_IndProp.LF.IndProp.Perm3_In x1 x3 x5 x7 x9 x11) (imported_Original_LF__DOT__IndProp_LF_IndProp_Perm3__In x10 x12).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_Perm3__In_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.Perm3_In ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_Perm3__In_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.Perm3_In imported_Original_LF__DOT__IndProp_LF_IndProp_Perm3__In ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_Perm3__In_iso; constructor : typeclass_instances.


End Interface.