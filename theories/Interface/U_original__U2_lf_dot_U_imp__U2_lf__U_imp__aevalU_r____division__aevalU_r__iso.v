From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aevalU_r____division__aexp__iso Interface.nat__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aevalU_r____division__aexp__iso Interface.nat__iso.

  Export Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aevalU_r____division__aexp__iso.CodeBlocks Interface.nat__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aevalU_r____division__aexp__iso.Interface <+ Interface.nat__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR : imported_Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp -> imported_nat -> SProp.
Parameter Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR_iso : forall (x1 : Original.LF_DOT_Imp.LF.Imp.aevalR_division.aexp) (x2 : imported_Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp),
  rel_iso Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp_iso x1 x2 ->
  forall (x3 : nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> Iso (Original.LF_DOT_Imp.LF.Imp.aevalR_division.aevalR x1 x3) (imported_Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR x2 x4).
Existing Instance Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.aevalR_division.aevalR ?x) => unify x Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.aevalR_division.aevalR imported_Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR ?x) => unify x Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR_iso; constructor : typeclass_instances.


End Interface.