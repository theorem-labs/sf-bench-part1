From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__aexp__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__aexp__iso.

  Export Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__aexp__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__aexp__iso.Args <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__aexp__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Imp_LF_Imp_AExp_APlus : imported_Original_LF__DOT__Imp_LF_Imp_AExp_aexp -> imported_Original_LF__DOT__Imp_LF_Imp_AExp_aexp -> imported_Original_LF__DOT__Imp_LF_Imp_AExp_aexp.
Parameter Original_LF__DOT__Imp_LF_Imp_AExp_APlus_iso : forall (x1 : Original.LF_DOT_Imp.LF.Imp.AExp.aexp) (x2 : imported_Original_LF__DOT__Imp_LF_Imp_AExp_aexp),
  rel_iso Original_LF__DOT__Imp_LF_Imp_AExp_aexp_iso x1 x2 ->
  forall (x3 : Original.LF_DOT_Imp.LF.Imp.AExp.aexp) (x4 : imported_Original_LF__DOT__Imp_LF_Imp_AExp_aexp),
  rel_iso Original_LF__DOT__Imp_LF_Imp_AExp_aexp_iso x3 x4 ->
  rel_iso Original_LF__DOT__Imp_LF_Imp_AExp_aexp_iso (Original.LF_DOT_Imp.LF.Imp.AExp.APlus x1 x3) (imported_Original_LF__DOT__Imp_LF_Imp_AExp_APlus x2 x4).
Existing Instance Original_LF__DOT__Imp_LF_Imp_AExp_APlus_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.AExp.APlus ?x) => unify x Original_LF__DOT__Imp_LF_Imp_AExp_APlus_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.AExp.APlus imported_Original_LF__DOT__Imp_LF_Imp_AExp_APlus ?x) => unify x Original_LF__DOT__Imp_LF_Imp_AExp_APlus_iso; constructor : typeclass_instances.


End Interface.