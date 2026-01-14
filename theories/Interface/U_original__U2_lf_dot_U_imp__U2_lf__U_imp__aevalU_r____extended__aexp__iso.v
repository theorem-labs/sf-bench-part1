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

Parameter imported_Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp : Type.
Parameter Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_iso : Iso Original.LF_DOT_Imp.LF.Imp.aevalR_extended.aexp imported_Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp.
Existing Instance Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.aevalR_extended.aexp ?x) => unify x Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.aevalR_extended.aexp imported_Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp ?x) => unify x Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp_iso; constructor : typeclass_instances.


End Interface.