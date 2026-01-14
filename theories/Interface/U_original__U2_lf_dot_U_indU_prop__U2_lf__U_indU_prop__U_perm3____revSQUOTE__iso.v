From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_perm3__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Interface.nat__iso Interface.U_s__iso Interface.__0__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_perm3__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Interface.nat__iso Interface.U_s__iso Interface.__0__iso.

  Export Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_perm3__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_perm3__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_Perm3__rev' : imported_Original_LF__DOT__IndProp_LF_IndProp_Perm3
    (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S imported_0)
       (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S imported_0))
          (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S imported_0))) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))))
    (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S imported_0)))
       (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S imported_0))
          (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S imported_0) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat)))).
Parameter Original_LF__DOT__IndProp_LF_IndProp_Perm3__rev'_iso : rel_iso
    (Original_LF__DOT__IndProp_LF_IndProp_Perm3_iso
       (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso _0_iso)
          (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso)) (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso _0_iso))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))))
       (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso _0_iso)))
          (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso)) (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso _0_iso) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)))))
    Original.LF_DOT_IndProp.LF.IndProp.Perm3_rev' imported_Original_LF__DOT__IndProp_LF_IndProp_Perm3__rev'.
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_Perm3__rev'_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.Perm3_rev' ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_Perm3__rev'_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.Perm3_rev' imported_Original_LF__DOT__IndProp_LF_IndProp_Perm3__rev' ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_Perm3__rev'_iso; constructor : typeclass_instances.


End Interface.