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

Parameter imported_Original_LF__DOT__Logic_LF_Logic_peirce : SProp.
Parameter Original_LF__DOT__Logic_LF_Logic_peirce_iso : Iso Original.LF_DOT_Logic.LF.Logic.peirce imported_Original_LF__DOT__Logic_LF_Logic_peirce.
Existing Instance Original_LF__DOT__Logic_LF_Logic_peirce_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.peirce ?x) => unify x Original_LF__DOT__Logic_LF_Logic_peirce_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.peirce imported_Original_LF__DOT__Logic_LF_Logic_peirce ?x) => unify x Original_LF__DOT__Logic_LF_Logic_peirce_iso; constructor : typeclass_instances.


End Interface.