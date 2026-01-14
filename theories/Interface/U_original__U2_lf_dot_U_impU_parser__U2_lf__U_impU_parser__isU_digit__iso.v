From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.bool__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.bool__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.bool__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.bool__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__ImpParser_LF_ImpParser_isDigit : imported_Ascii_ascii -> imported_bool.
Parameter Original_LF__DOT__ImpParser_LF_ImpParser_isDigit_iso : forall (x1 : Ascii.ascii) (x2 : imported_Ascii_ascii),
  rel_iso Ascii_ascii_iso x1 x2 -> rel_iso bool_iso (Original.LF_DOT_ImpParser.LF.ImpParser.isDigit x1) (imported_Original_LF__DOT__ImpParser_LF_ImpParser_isDigit x2).
Existing Instance Original_LF__DOT__ImpParser_LF_ImpParser_isDigit_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_ImpParser.LF.ImpParser.isDigit ?x) => unify x Original_LF__DOT__ImpParser_LF_ImpParser_isDigit_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_ImpParser.LF.ImpParser.isDigit imported_Original_LF__DOT__ImpParser_LF_ImpParser_isDigit ?x) => unify x Original_LF__DOT__ImpParser_LF_ImpParser_isDigit_iso; constructor : typeclass_instances.


End Interface.