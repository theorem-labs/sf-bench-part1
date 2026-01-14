From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_perm3U_reminder__U_perm3__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_perm3U_reminder__U_perm3__iso.

  Export Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_perm3U_reminder__U_perm3__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_perm3U_reminder__U_perm3__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_Perm3__symm : forall (x : Type) (x0 x1 : imported_Original_LF__DOT__Poly_LF_Poly_list x),
  imported_Original_LF__DOT__IndProp_LF_IndProp_Perm3Reminder_Perm3 x0 x1 -> imported_Original_LF__DOT__IndProp_LF_IndProp_Perm3Reminder_Perm3 x1 x0.
Parameter Original_LF__DOT__IndProp_LF_IndProp_Perm3__symm_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_Poly.LF.Poly.list x1) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2)
    (hx0 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x3 x4) (x5 : Original.LF_DOT_Poly.LF.Poly.list x1) (x6 : imported_Original_LF__DOT__Poly_LF_Poly_list x2)
    (hx1 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x5 x6) (x7 : Original.LF_DOT_IndProp.LF.IndProp.Perm3Reminder.Perm3 x3 x5)
    (x8 : imported_Original_LF__DOT__IndProp_LF_IndProp_Perm3Reminder_Perm3 x4 x6),
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_Perm3Reminder_Perm3_iso hx0 hx1) x7 x8 ->
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_Perm3Reminder_Perm3_iso hx1 hx0) (Original.LF_DOT_IndProp.LF.IndProp.Perm3_symm x1 x3 x5 x7)
    (imported_Original_LF__DOT__IndProp_LF_IndProp_Perm3__symm x8).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_Perm3__symm_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.Perm3_symm ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_Perm3__symm_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.Perm3_symm imported_Original_LF__DOT__IndProp_LF_IndProp_Perm3__symm ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_Perm3__symm_iso; constructor : typeclass_instances.


End Interface.