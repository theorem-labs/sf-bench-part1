From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bexp__iso Interface.bool__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bexp__iso Interface.bool__iso.

  Export Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bexp__iso.CodeBlocks Interface.bool__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aexp__bexp__iso.Interface <+ Interface.bool__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Imp_LF_Imp_AExp_bevalR : imported_Original_LF__DOT__Imp_LF_Imp_AExp_bexp -> imported_bool -> SProp.
Parameter Original_LF__DOT__Imp_LF_Imp_AExp_bevalR_iso : forall (x1 : Original.LF_DOT_Imp.LF.Imp.AExp.bexp) (x2 : imported_Original_LF__DOT__Imp_LF_Imp_AExp_bexp),
  rel_iso Original_LF__DOT__Imp_LF_Imp_AExp_bexp_iso x1 x2 ->
  forall (x3 : bool) (x4 : imported_bool), rel_iso bool_iso x3 x4 -> Iso (Original.LF_DOT_Imp.LF.Imp.AExp.bevalR x1 x3) (imported_Original_LF__DOT__Imp_LF_Imp_AExp_bevalR x2 x4).
Existing Instance Original_LF__DOT__Imp_LF_Imp_AExp_bevalR_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.AExp.bevalR ?x) => unify x Original_LF__DOT__Imp_LF_Imp_AExp_bevalR_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.AExp.bevalR imported_Original_LF__DOT__Imp_LF_Imp_AExp_bevalR ?x) => unify x Original_LF__DOT__Imp_LF_Imp_AExp_bevalR_iso; constructor : typeclass_instances.


End Interface.