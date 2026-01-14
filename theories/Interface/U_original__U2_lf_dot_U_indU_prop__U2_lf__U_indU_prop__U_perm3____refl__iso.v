From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_perm3__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_perm3__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.

  Export Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_perm3__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_perm3__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_Perm3__refl : forall (x : Type) (x0 x1 x2 : x),
  imported_Original_LF__DOT__IndProp_LF_IndProp_Perm3
    (imported_Original_LF__DOT__Poly_LF_Poly_cons x0
       (imported_Original_LF__DOT__Poly_LF_Poly_cons x1 (imported_Original_LF__DOT__Poly_LF_Poly_cons x2 (imported_Original_LF__DOT__Poly_LF_Poly_nil x))))
    (imported_Original_LF__DOT__Poly_LF_Poly_cons x0
       (imported_Original_LF__DOT__Poly_LF_Poly_cons x1 (imported_Original_LF__DOT__Poly_LF_Poly_cons x2 (imported_Original_LF__DOT__Poly_LF_Poly_nil x)))).
Parameter Original_LF__DOT__IndProp_LF_IndProp_Perm3__refl_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (hx0 : rel_iso hx x3 x4) (x5 : x1) (x6 : x2) (hx1 : rel_iso hx x5 x6) (x7 : x1) (x8 : x2) (hx2 : rel_iso hx x7 x8),
  rel_iso
    (Original_LF__DOT__IndProp_LF_IndProp_Perm3_iso
       (Original_LF__DOT__Poly_LF_Poly_cons_iso hx0 (Original_LF__DOT__Poly_LF_Poly_cons_iso hx1 (Original_LF__DOT__Poly_LF_Poly_cons_iso hx2 (Original_LF__DOT__Poly_LF_Poly_nil_iso hx))))
       (Original_LF__DOT__Poly_LF_Poly_cons_iso hx0 (Original_LF__DOT__Poly_LF_Poly_cons_iso hx1 (Original_LF__DOT__Poly_LF_Poly_cons_iso hx2 (Original_LF__DOT__Poly_LF_Poly_nil_iso hx)))))
    (Original.LF_DOT_IndProp.LF.IndProp.Perm3_refl x1 x3 x5 x7) (imported_Original_LF__DOT__IndProp_LF_IndProp_Perm3__refl x4 x6 x8).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_Perm3__refl_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.Perm3_refl ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_Perm3__refl_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.Perm3_refl imported_Original_LF__DOT__IndProp_LF_IndProp_Perm3__refl ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_Perm3__refl_iso; constructor : typeclass_instances.


End Interface.