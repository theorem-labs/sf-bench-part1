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

Parameter imported_Original_LF__DOT__ImpParser_LF_ImpParser_optionE : Type -> Type.
Parameter Original_LF__DOT__ImpParser_LF_ImpParser_optionE_iso : forall x1 x2 : Type, Iso x1 x2 -> Iso (Original.LF_DOT_ImpParser.LF.ImpParser.optionE x1) (imported_Original_LF__DOT__ImpParser_LF_ImpParser_optionE x2).
Existing Instance Original_LF__DOT__ImpParser_LF_ImpParser_optionE_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_ImpParser.LF.ImpParser.optionE ?x) => unify x Original_LF__DOT__ImpParser_LF_ImpParser_optionE_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_ImpParser.LF.ImpParser.optionE imported_Original_LF__DOT__ImpParser_LF_ImpParser_optionE ?x) => unify x Original_LF__DOT__ImpParser_LF_ImpParser_optionE_iso; constructor : typeclass_instances.


End Interface.