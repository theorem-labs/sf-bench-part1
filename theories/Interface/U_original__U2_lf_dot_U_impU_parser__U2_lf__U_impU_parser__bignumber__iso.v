From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.nat__iso.

Module Export CodeBlocks.

  Export (hints) Interface.nat__iso.

  Export Interface.nat__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.nat__iso.Args <+ Interface.nat__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__ImpParser_LF_ImpParser_bignumber : imported_nat.
Parameter Original_LF__DOT__ImpParser_LF_ImpParser_bignumber_iso : rel_iso nat_iso Original.LF_DOT_ImpParser.LF.ImpParser.bignumber imported_Original_LF__DOT__ImpParser_LF_ImpParser_bignumber.
Existing Instance Original_LF__DOT__ImpParser_LF_ImpParser_bignumber_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_ImpParser.LF.ImpParser.bignumber ?x) => unify x Original_LF__DOT__ImpParser_LF_ImpParser_bignumber_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_ImpParser.LF.ImpParser.bignumber imported_Original_LF__DOT__ImpParser_LF_ImpParser_bignumber ?x) => unify x Original_LF__DOT__ImpParser_LF_ImpParser_bignumber_iso; constructor : typeclass_instances.


End Interface.