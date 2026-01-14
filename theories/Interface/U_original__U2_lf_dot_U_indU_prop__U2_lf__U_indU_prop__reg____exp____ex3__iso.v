From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_false__iso Interface.U_logic__not__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_char__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Interface.nat__iso Interface.U_s__iso Interface.__0__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_false__iso Interface.U_logic__not__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_char__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Interface.nat__iso Interface.U_s__iso Interface.__0__iso.

  Export Interface.U_false__iso.CodeBlocks Interface.U_logic__not__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_char__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_false__iso.Interface <+ Interface.U_logic__not__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_char__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp__ex3 : imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match
    (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S imported_0)
       (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S imported_0)) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat)))
    (imported_Original_LF__DOT__IndProp_LF_IndProp_Char (imported_S imported_0)) ->
  imported_False.
Parameter Original_LF__DOT__IndProp_LF_IndProp_reg__exp__ex3_iso : forall
    (x1 : Original.LF_DOT_IndProp.LF.IndProp.exp_match (Original.LF_DOT_Poly.LF.Poly.cons 1 (Original.LF_DOT_Poly.LF.Poly.cons 2 Original.LF_DOT_Poly.LF.Poly.nil))
            (Original.LF_DOT_IndProp.LF.IndProp.Char 1))
    (x2 : imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match
            (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S imported_0)
               (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S imported_0)) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat)))
            (imported_Original_LF__DOT__IndProp_LF_IndProp_Char (imported_S imported_0))),
  rel_iso
    (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso
       (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso _0_iso) (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso)) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)))
       (Original_LF__DOT__IndProp_LF_IndProp_Char_iso (S_iso _0_iso)))
    x1 x2 ->
  rel_iso False_iso (Original.LF_DOT_IndProp.LF.IndProp.reg_exp_ex3 x1) (imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp__ex3 x2).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_reg__exp__ex3_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.reg_exp_ex3 ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_reg__exp__ex3_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.reg_exp_ex3 imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp__ex3 ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_reg__exp__ex3_iso; constructor : typeclass_instances.


End Interface.