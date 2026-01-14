From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__bexp__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__bexp__iso.

  Export Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__bexp__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__bexp__iso.Args <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__bexp__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Imp_LF_Imp_example__bexp : imported_Original_LF__DOT__Imp_LF_Imp_bexp.
Parameter Original_LF__DOT__Imp_LF_Imp_example__bexp_iso : rel_iso Original_LF__DOT__Imp_LF_Imp_bexp_iso Original.LF_DOT_Imp.LF.Imp.example_bexp imported_Original_LF__DOT__Imp_LF_Imp_example__bexp.
Existing Instance Original_LF__DOT__Imp_LF_Imp_example__bexp_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.example_bexp ?x) => unify x Original_LF__DOT__Imp_LF_Imp_example__bexp_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.example_bexp imported_Original_LF__DOT__Imp_LF_Imp_example__bexp ?x) => unify x Original_LF__DOT__Imp_LF_Imp_example__bexp_iso; constructor : typeclass_instances.


End Interface.