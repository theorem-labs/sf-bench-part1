From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_string__string__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_string__string__iso.

  Export Interface.U_string__string__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_string__string__iso.Args <+ Interface.U_string__string__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Imp_LF_Imp_X : imported_String_string.
Parameter Original_LF__DOT__Imp_LF_Imp_X_iso : rel_iso String_string_iso Original.LF_DOT_Imp.LF.Imp.X imported_Original_LF__DOT__Imp_LF_Imp_X.
Existing Instance Original_LF__DOT__Imp_LF_Imp_X_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.X ?x) => unify x Original_LF__DOT__Imp_LF_Imp_X_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.X imported_Original_LF__DOT__Imp_LF_Imp_X ?x) => unify x Original_LF__DOT__Imp_LF_Imp_X_iso; constructor : typeclass_instances.


End Interface.