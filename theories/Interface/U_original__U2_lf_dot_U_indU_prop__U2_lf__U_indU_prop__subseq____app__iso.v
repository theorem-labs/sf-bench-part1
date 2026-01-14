From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__subseq__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__subseq__iso.

  Export Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__subseq__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__subseq__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_subseq__app : forall x x0 x1 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat,
  imported_Original_LF__DOT__IndProp_LF_IndProp_subseq x x0 -> imported_Original_LF__DOT__IndProp_LF_IndProp_subseq x (imported_Original_LF__DOT__Poly_LF_Poly_app x0 x1).
Parameter Original_LF__DOT__IndProp_LF_IndProp_subseq__app_iso : forall (x1 : Original.LF_DOT_Poly.LF.Poly.list nat) (x2 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat) (hx : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso nat_iso) x1 x2)
    (x3 : Original.LF_DOT_Poly.LF.Poly.list nat) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat) (hx0 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso nat_iso) x3 x4)
    (x5 : Original.LF_DOT_Poly.LF.Poly.list nat) (x6 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_nat) (hx1 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso nat_iso) x5 x6)
    (x7 : Original.LF_DOT_IndProp.LF.IndProp.subseq x1 x3) (x8 : imported_Original_LF__DOT__IndProp_LF_IndProp_subseq x2 x4),
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_subseq_iso hx hx0) x7 x8 ->
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_subseq_iso hx (Original_LF__DOT__Poly_LF_Poly_app_iso hx0 hx1)) (Original.LF_DOT_IndProp.LF.IndProp.subseq_app x1 x3 x5 x7)
    (imported_Original_LF__DOT__IndProp_LF_IndProp_subseq__app x6 x8).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_subseq__app_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.subseq_app ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_subseq__app_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.subseq_app imported_Original_LF__DOT__IndProp_LF_IndProp_subseq__app ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_subseq__app_iso; constructor : typeclass_instances.


End Interface.