From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_false__iso Interface.U_logic__not__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_perm3U_reminder__U_perm3__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Interface.nat__iso Interface.U_s__iso Interface.__0__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_false__iso Interface.U_logic__not__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_perm3U_reminder__U_perm3__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Interface.nat__iso Interface.U_s__iso Interface.__0__iso.

  Export Interface.U_false__iso.CodeBlocks Interface.U_logic__not__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_perm3U_reminder__U_perm3__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_false__iso.Interface <+ Interface.U_logic__not__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_perm3U_reminder__U_perm3__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_Perm3__example2 : imported_Original_LF__DOT__IndProp_LF_IndProp_Perm3Reminder_Perm3
    (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S imported_0)
       (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S imported_0))
          (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S imported_0))) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))))
    (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S imported_0)
       (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S imported_0))
          (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0)))) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat)))) ->
  imported_False.
Parameter Original_LF__DOT__IndProp_LF_IndProp_Perm3__example2_iso : forall
    (x1 : Original.LF_DOT_IndProp.LF.IndProp.Perm3Reminder.Perm3
            (Original.LF_DOT_Poly.LF.Poly.cons 1 (Original.LF_DOT_Poly.LF.Poly.cons 2 (Original.LF_DOT_Poly.LF.Poly.cons 3 Original.LF_DOT_Poly.LF.Poly.nil)))
            (Original.LF_DOT_Poly.LF.Poly.cons 1 (Original.LF_DOT_Poly.LF.Poly.cons 2 (Original.LF_DOT_Poly.LF.Poly.cons 4 Original.LF_DOT_Poly.LF.Poly.nil))))
    (x2 : imported_Original_LF__DOT__IndProp_LF_IndProp_Perm3Reminder_Perm3
            (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S imported_0)
               (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S imported_0))
                  (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S imported_0))) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))))
            (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S imported_0)
               (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S imported_0))
                  (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0)))) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat))))),
  rel_iso
    (Original_LF__DOT__IndProp_LF_IndProp_Perm3Reminder_Perm3_iso
       (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso _0_iso)
          (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso)) (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso _0_iso))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso))))
       (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso _0_iso)
          (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso))
             (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 1 0 imported_0 _0_iso)))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)))))
    x1 x2 ->
  rel_iso False_iso (Original.LF_DOT_IndProp.LF.IndProp.Perm3_example2 x1) (imported_Original_LF__DOT__IndProp_LF_IndProp_Perm3__example2 x2).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_Perm3__example2_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.Perm3_example2 ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_Perm3__example2_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.Perm3_example2 imported_Original_LF__DOT__IndProp_LF_IndProp_Perm3__example2 ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_Perm3__example2_iso; constructor : typeclass_instances.


End Interface.