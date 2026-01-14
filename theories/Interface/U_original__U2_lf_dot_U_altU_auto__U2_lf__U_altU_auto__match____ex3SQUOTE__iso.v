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

Parameter imported_Original_LF__DOT__AltAuto_LF_AltAuto_match__ex3' : forall x : SProp, x -> x.
Parameter Original_LF__DOT__AltAuto_LF_AltAuto_match__ex3'_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2),
  rel_iso hx x3 x4 -> rel_iso hx (Original.LF_DOT_AltAuto.LF.AltAuto.match_ex3' x1 x3) (imported_Original_LF__DOT__AltAuto_LF_AltAuto_match__ex3' x4).
Existing Instance Original_LF__DOT__AltAuto_LF_AltAuto_match__ex3'_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.match_ex3' ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_match__ex3'_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.match_ex3' imported_Original_LF__DOT__AltAuto_LF_AltAuto_match__ex3' ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_match__ex3'_iso; constructor : typeclass_instances.


End Interface.