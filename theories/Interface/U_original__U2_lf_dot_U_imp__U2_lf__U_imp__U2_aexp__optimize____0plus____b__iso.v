From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bexp__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bexp__iso.

  Export Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bexp__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bexp__iso.Args <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bexp__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b : imported_Original_LF__DOT__Imp_LF_Imp_AExp_bexp -> imported_Original_LF__DOT__Imp_LF_Imp_AExp_bexp.
Parameter Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b_iso : forall (x1 : Original.LF_DOT_Imp.LF.Imp.AExp.bexp) (x2 : imported_Original_LF__DOT__Imp_LF_Imp_AExp_bexp),
  rel_iso Original_LF__DOT__Imp_LF_Imp_AExp_bexp_iso x1 x2 ->
  rel_iso Original_LF__DOT__Imp_LF_Imp_AExp_bexp_iso (Original.LF_DOT_Imp.LF.Imp.AExp.optimize_0plus_b x1) (imported_Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b x2).
Existing Instance Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.AExp.optimize_0plus_b ?x) => unify x Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.AExp.optimize_0plus_b imported_Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b ?x) => unify x Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__b_iso; constructor : typeclass_instances.


End Interface.