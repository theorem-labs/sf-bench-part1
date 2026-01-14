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

Parameter imported_Original_LF__DOT__AltAuto_LF_AltAuto_imp2 : forall x x0 : SProp, x -> (x -> x0) -> x0.
Parameter Original_LF__DOT__AltAuto_LF_AltAuto_imp2_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : Prop) (x4 : SProp) (hx0 : Iso x3 x4) (x5 : x1) (x6 : x2),
  rel_iso hx x5 x6 ->
  forall (x7 : x1 -> x3) (x8 : x2 -> x4),
  (forall (x9 : x1) (x10 : x2), rel_iso hx x9 x10 -> rel_iso hx0 (x7 x9) (x8 x10)) ->
  rel_iso hx0 (Original.LF_DOT_AltAuto.LF.AltAuto.imp2 x1 x3 x5 x7) (imported_Original_LF__DOT__AltAuto_LF_AltAuto_imp2 x6 x8).
Existing Instance Original_LF__DOT__AltAuto_LF_AltAuto_imp2_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.imp2 ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_imp2_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.imp2 imported_Original_LF__DOT__AltAuto_LF_AltAuto_imp2 ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_imp2_iso; constructor : typeclass_instances.


End Interface.