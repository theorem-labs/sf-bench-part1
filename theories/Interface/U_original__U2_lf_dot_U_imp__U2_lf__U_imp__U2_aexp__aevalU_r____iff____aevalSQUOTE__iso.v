From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__aexp__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.iff__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__aevalU_r__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__aeval__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__aexp__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.iff__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__aevalU_r__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__aeval__iso.

  Export Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__aexp__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.iff__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__aevalU_r__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__aeval__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__aexp__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.iff__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__aevalU_r__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__aeval__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__iff__aeval' : forall (x : imported_Original_LF__DOT__Imp_LF_Imp_AExp_aexp) (x0 : imported_nat),
  imported_iff (imported_Original_LF__DOT__Imp_LF_Imp_AExp_aevalR x x0) (imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Imp_LF_Imp_AExp_aeval x) x0).
Parameter Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__iff__aeval'_iso : forall (x1 : Original.LF_DOT_Imp.LF.Imp.AExp.aexp) (x2 : imported_Original_LF__DOT__Imp_LF_Imp_AExp_aexp) (hx : rel_iso Original_LF__DOT__Imp_LF_Imp_AExp_aexp_iso x1 x2) 
    (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4),
  rel_iso
    {|
      to := iff_iso (Original_LF__DOT__Imp_LF_Imp_AExp_aevalR_iso hx hx0) (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Imp_LF_Imp_AExp_aeval_iso hx) hx0);
      from := from (iff_iso (Original_LF__DOT__Imp_LF_Imp_AExp_aevalR_iso hx hx0) (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Imp_LF_Imp_AExp_aeval_iso hx) hx0));
      to_from :=
        fun x : imported_iff (imported_Original_LF__DOT__Imp_LF_Imp_AExp_aevalR x2 x4) (imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Imp_LF_Imp_AExp_aeval x2) x4) =>
        to_from (iff_iso (Original_LF__DOT__Imp_LF_Imp_AExp_aevalR_iso hx hx0) (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Imp_LF_Imp_AExp_aeval_iso hx) hx0)) x;
      from_to :=
        fun x : Original.LF_DOT_Imp.LF.Imp.AExp.aevalR x1 x3 <-> Original.LF_DOT_Imp.LF.Imp.AExp.aeval x1 = x3 =>
        seq_p_of_t (from_to (iff_iso (Original_LF__DOT__Imp_LF_Imp_AExp_aevalR_iso hx hx0) (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Imp_LF_Imp_AExp_aeval_iso hx) hx0)) x)
    |} (Original.LF_DOT_Imp.LF.Imp.AExp.aevalR_iff_aeval' x1 x3) (imported_Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__iff__aeval' x2 x4).
Existing Instance Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__iff__aeval'_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.AExp.aevalR_iff_aeval' ?x) => unify x Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__iff__aeval'_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.AExp.aevalR_iff_aeval' imported_Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__iff__aeval' ?x) => unify x Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__iff__aeval'_iso; constructor : typeclass_instances.


End Interface.