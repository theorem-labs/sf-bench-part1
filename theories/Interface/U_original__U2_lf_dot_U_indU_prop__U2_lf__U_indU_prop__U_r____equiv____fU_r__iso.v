From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.iff__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_r__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__fU_r__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.iff__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_r__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__fU_r__iso.

  Export Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.iff__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_r__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__fU_r__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.iff__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_r__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__fU_r__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_R__equiv__fR : forall x x0 x1 : imported_nat, imported_iff (imported_Original_LF__DOT__IndProp_LF_IndProp_R x x0 x1) (imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__IndProp_LF_IndProp_fR x x0) x1).
Parameter Original_LF__DOT__IndProp_LF_IndProp_R__equiv__fR_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) (x5 : nat) (x6 : imported_nat) (hx1 : rel_iso nat_iso x5 x6),
  rel_iso
    {|
      to := iff_iso (Original_LF__DOT__IndProp_LF_IndProp_R_iso hx hx0 hx1) (Corelib_Init_Logic_eq_iso (Original_LF__DOT__IndProp_LF_IndProp_fR_iso hx hx0) hx1);
      from := from (iff_iso (Original_LF__DOT__IndProp_LF_IndProp_R_iso hx hx0 hx1) (Corelib_Init_Logic_eq_iso (Original_LF__DOT__IndProp_LF_IndProp_fR_iso hx hx0) hx1));
      to_from :=
        fun x : imported_iff (imported_Original_LF__DOT__IndProp_LF_IndProp_R x2 x4 x6) (imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__IndProp_LF_IndProp_fR x2 x4) x6) =>
        to_from (iff_iso (Original_LF__DOT__IndProp_LF_IndProp_R_iso hx hx0 hx1) (Corelib_Init_Logic_eq_iso (Original_LF__DOT__IndProp_LF_IndProp_fR_iso hx hx0) hx1)) x;
      from_to :=
        fun x : Original.LF_DOT_IndProp.LF.IndProp.R x1 x3 x5 <-> Original.LF_DOT_IndProp.LF.IndProp.fR x1 x3 = x5 =>
        seq_p_of_t (from_to (iff_iso (Original_LF__DOT__IndProp_LF_IndProp_R_iso hx hx0 hx1) (Corelib_Init_Logic_eq_iso (Original_LF__DOT__IndProp_LF_IndProp_fR_iso hx hx0) hx1)) x)
    |} (Original.LF_DOT_IndProp.LF.IndProp.R_equiv_fR x1 x3 x5) (imported_Original_LF__DOT__IndProp_LF_IndProp_R__equiv__fR x2 x4 x6).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_R__equiv__fR_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.R_equiv_fR ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_R__equiv__fR_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.R_equiv_fR imported_Original_LF__DOT__IndProp_LF_IndProp_R__equiv__fR ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_R__equiv__fR_iso; constructor : typeclass_instances.


End Interface.