From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

Module Export CodeBlocks.

End CodeBlocks.

Module Type Args. End Args.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_com : Type.
Parameter Original_LF__DOT__Imp_LF_Imp_BreakImp_com_iso : Iso Original.LF_DOT_Imp.LF.Imp.BreakImp.com imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_com.
Existing Instance Original_LF__DOT__Imp_LF_Imp_BreakImp_com_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.BreakImp.com ?x) => unify x Original_LF__DOT__Imp_LF_Imp_BreakImp_com_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.BreakImp.com imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_com ?x) => unify x Original_LF__DOT__Imp_LF_Imp_BreakImp_com_iso; constructor : typeclass_instances.


End Interface.