From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_true__iso Interface.and__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_true__iso Interface.and__iso.

  Export Interface.U_true__iso.CodeBlocks Interface.and__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_true__iso.Interface <+ Interface.and__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__AltAuto_LF_AltAuto_match__ex2 : imported_and imported_True imported_True.
Parameter Original_LF__DOT__AltAuto_LF_AltAuto_match__ex2_iso : rel_iso (relax_Iso_Ts_Ps (and_iso True_iso True_iso)) Original.LF_DOT_AltAuto.LF.AltAuto.match_ex2 imported_Original_LF__DOT__AltAuto_LF_AltAuto_match__ex2.
Existing Instance Original_LF__DOT__AltAuto_LF_AltAuto_match__ex2_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.match_ex2 ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_match__ex2_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.match_ex2 imported_Original_LF__DOT__AltAuto_LF_AltAuto_match__ex2 ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_match__ex2_iso; constructor : typeclass_instances.


End Interface.