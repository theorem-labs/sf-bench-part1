From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_true__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_true__iso.

  Export Interface.U_true__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_true__iso.Args <+ Interface.U_true__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__AltAuto_LF_AltAuto_match__ex1 : imported_True.
Parameter Original_LF__DOT__AltAuto_LF_AltAuto_match__ex1_iso : rel_iso True_iso Original.LF_DOT_AltAuto.LF.AltAuto.match_ex1 imported_Original_LF__DOT__AltAuto_LF_AltAuto_match__ex1.
Existing Instance Original_LF__DOT__AltAuto_LF_AltAuto_match__ex1_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.match_ex1 ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_match__ex1_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.match_ex1 imported_Original_LF__DOT__AltAuto_LF_AltAuto_match__ex1 ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_match__ex1_iso; constructor : typeclass_instances.


End Interface.