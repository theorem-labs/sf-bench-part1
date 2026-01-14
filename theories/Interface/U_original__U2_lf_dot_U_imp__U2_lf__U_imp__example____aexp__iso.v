From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso.

  Export Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso.Args <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Imp_LF_Imp_example__aexp : imported_Original_LF__DOT__Imp_LF_Imp_aexp.
Parameter Original_LF__DOT__Imp_LF_Imp_example__aexp_iso : rel_iso Original_LF__DOT__Imp_LF_Imp_aexp_iso Original.LF_DOT_Imp.LF.Imp.example_aexp imported_Original_LF__DOT__Imp_LF_Imp_example__aexp.
Existing Instance Original_LF__DOT__Imp_LF_Imp_example__aexp_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.example_aexp ?x) => unify x Original_LF__DOT__Imp_LF_Imp_example__aexp_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.example_aexp imported_Original_LF__DOT__Imp_LF_Imp_example__aexp ?x) => unify x Original_LF__DOT__Imp_LF_Imp_example__aexp_iso; constructor : typeclass_instances.


End Interface.