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

Parameter imported_Original_LF__DOT__Logic_LF_Logic_implies__to__or : SProp.
Parameter Original_LF__DOT__Logic_LF_Logic_implies__to__or_iso : Iso Original.LF_DOT_Logic.LF.Logic.implies_to_or imported_Original_LF__DOT__Logic_LF_Logic_implies__to__or.
Existing Instance Original_LF__DOT__Logic_LF_Logic_implies__to__or_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.implies_to_or ?x) => unify x Original_LF__DOT__Logic_LF_Logic_implies__to__or_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.implies_to_or imported_Original_LF__DOT__Logic_LF_Logic_implies__to__or ?x) => unify x Original_LF__DOT__Logic_LF_Logic_implies__to__or_iso; constructor : typeclass_instances.


End Interface.