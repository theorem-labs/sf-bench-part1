From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__re____not____empty__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.ex__iso Interface.iff__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__re____not____empty__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.ex__iso Interface.iff__iso.

  Export Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__re____not____empty__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.ex__iso.CodeBlocks Interface.iff__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__re____not____empty__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.ex__iso.Interface <+ Interface.iff__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_re__not__empty__correct : forall (x : Type) (x0 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp x),
  imported_iff (imported_ex (fun H : imported_Original_LF__DOT__Poly_LF_Poly_list x => imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match H x0))
    (imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__IndProp_LF_IndProp_re__not__empty x0) imported_Original_LF__DOT__Basics_LF_Basics_true).
Parameter Original_LF__DOT__IndProp_LF_IndProp_re__not__empty__correct_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_IndProp.LF.IndProp.reg_exp x1) (x4 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp x2)
    (hx0 : rel_iso (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) x3 x4),
  rel_iso
    (relax_Iso_Ts_Ps
       (iff_iso
          (ex_iso (fun s : Original.LF_DOT_Poly.LF.Poly.list x1 => Original.LF_DOT_IndProp.LF.IndProp.exp_match s x3)
             (fun H : imported_Original_LF__DOT__Poly_LF_Poly_list x2 => imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match H x4)
             (fun (x5 : Original.LF_DOT_Poly.LF.Poly.list x1) (x6 : imported_Original_LF__DOT__Poly_LF_Poly_list x2) (hx1 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x5 x6) =>
              Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso hx1 hx0))
          (Corelib_Init_Logic_eq_iso (Original_LF__DOT__IndProp_LF_IndProp_re__not__empty_iso hx0) Original_LF__DOT__Basics_LF_Basics_true_iso)))
    (Original.LF_DOT_IndProp.LF.IndProp.re_not_empty_correct x1 x3) (imported_Original_LF__DOT__IndProp_LF_IndProp_re__not__empty__correct x4).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_re__not__empty__correct_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.re_not_empty_correct ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_re__not__empty__correct_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.re_not_empty_correct imported_Original_LF__DOT__IndProp_LF_IndProp_re__not__empty__correct ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_re__not__empty__correct_iso; constructor : typeclass_instances.


End Interface.