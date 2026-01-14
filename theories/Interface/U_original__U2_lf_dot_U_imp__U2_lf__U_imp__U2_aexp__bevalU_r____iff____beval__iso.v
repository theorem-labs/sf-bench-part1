From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bexp__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bevalU_r__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__beval__iso Interface.iff__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bexp__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bevalU_r__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__beval__iso Interface.iff__iso.

  Export Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bexp__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.bool__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bevalU_r__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__beval__iso.CodeBlocks Interface.iff__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bexp__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.bool__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bevalU_r__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__beval__iso.Interface <+ Interface.iff__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Imp_LF_Imp_AExp_bevalR__iff__beval : forall (x : imported_Original_LF__DOT__Imp_LF_Imp_AExp_bexp) (x0 : imported_bool),
  imported_iff (imported_Original_LF__DOT__Imp_LF_Imp_AExp_bevalR x x0) (imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Imp_LF_Imp_AExp_beval x) x0).
Parameter Original_LF__DOT__Imp_LF_Imp_AExp_bevalR__iff__beval_iso : forall (x1 : Original.LF_DOT_Imp.LF.Imp.AExp.bexp) (x2 : imported_Original_LF__DOT__Imp_LF_Imp_AExp_bexp) (hx : rel_iso Original_LF__DOT__Imp_LF_Imp_AExp_bexp_iso x1 x2) 
    (x3 : bool) (x4 : imported_bool) (hx0 : rel_iso bool_iso x3 x4),
  rel_iso
    {|
      to := iff_iso (Original_LF__DOT__Imp_LF_Imp_AExp_bevalR_iso hx hx0) (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Imp_LF_Imp_AExp_beval_iso hx) hx0);
      from := from (iff_iso (Original_LF__DOT__Imp_LF_Imp_AExp_bevalR_iso hx hx0) (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Imp_LF_Imp_AExp_beval_iso hx) hx0));
      to_from :=
        fun x : imported_iff (imported_Original_LF__DOT__Imp_LF_Imp_AExp_bevalR x2 x4) (imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Imp_LF_Imp_AExp_beval x2) x4) =>
        to_from (iff_iso (Original_LF__DOT__Imp_LF_Imp_AExp_bevalR_iso hx hx0) (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Imp_LF_Imp_AExp_beval_iso hx) hx0)) x;
      from_to :=
        fun x : Original.LF_DOT_Imp.LF.Imp.AExp.bevalR x1 x3 <-> Original.LF_DOT_Imp.LF.Imp.AExp.beval x1 = x3 =>
        seq_p_of_t (from_to (iff_iso (Original_LF__DOT__Imp_LF_Imp_AExp_bevalR_iso hx hx0) (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Imp_LF_Imp_AExp_beval_iso hx) hx0)) x)
    |} (Original.LF_DOT_Imp.LF.Imp.AExp.bevalR_iff_beval x1 x3) (imported_Original_LF__DOT__Imp_LF_Imp_AExp_bevalR__iff__beval x2 x4).
Existing Instance Original_LF__DOT__Imp_LF_Imp_AExp_bevalR__iff__beval_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.AExp.bevalR_iff_beval ?x) => unify x Original_LF__DOT__Imp_LF_Imp_AExp_bevalR__iff__beval_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.AExp.bevalR_iff_beval imported_Original_LF__DOT__Imp_LF_Imp_AExp_bevalR__iff__beval ?x) => unify x Original_LF__DOT__Imp_LF_Imp_AExp_bevalR__iff__beval_iso; constructor : typeclass_instances.


End Interface.