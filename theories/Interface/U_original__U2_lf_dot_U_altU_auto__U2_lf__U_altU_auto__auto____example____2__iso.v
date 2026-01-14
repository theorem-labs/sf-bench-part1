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

Parameter imported_Original_LF__DOT__AltAuto_LF_AltAuto_auto__example__2 : forall x x0 x1 x2 x3 x4 : SProp, (x -> x0) -> (x -> x1) -> (x3 -> x1) -> (x2 -> x3 -> x4) -> ((x -> x0) -> x -> x2) -> x3 -> x -> x4.
Parameter Original_LF__DOT__AltAuto_LF_AltAuto_auto__example__2_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : Prop) (x4 : SProp) (hx0 : Iso x3 x4) (x5 : Prop) (x6 : SProp) (hx1 : Iso x5 x6) (x7 : Prop) (x8 : SProp) (hx2 : Iso x7 x8) 
    (x9 : Prop) (x10 : SProp) (hx3 : Iso x9 x10) (x11 : Prop) (x12 : SProp) (hx4 : Iso x11 x12) (x13 : x1 -> x3) (x14 : x2 -> x4),
  (forall (x15 : x1) (x16 : x2), rel_iso hx x15 x16 -> rel_iso hx0 (x13 x15) (x14 x16)) ->
  forall (x15 : x1 -> x5) (x16 : x2 -> x6),
  (forall (x17 : x1) (x18 : x2), rel_iso hx x17 x18 -> rel_iso hx1 (x15 x17) (x16 x18)) ->
  forall (x17 : x9 -> x5) (x18 : x10 -> x6),
  (forall (x19 : x9) (x20 : x10), rel_iso hx3 x19 x20 -> rel_iso hx1 (x17 x19) (x18 x20)) ->
  forall (x19 : x7 -> x9 -> x11) (x20 : x8 -> x10 -> x12),
  (forall (x21 : x7) (x22 : x8), rel_iso hx2 x21 x22 -> forall (x23 : x9) (x24 : x10), rel_iso hx3 x23 x24 -> rel_iso hx4 (x19 x21 x23) (x20 x22 x24)) ->
  forall (x21 : (x1 -> x3) -> x1 -> x7) (x22 : (x2 -> x4) -> x2 -> x8),
  (forall (x23 : x1 -> x3) (x24 : x2 -> x4),
   (forall (x25 : x1) (x26 : x2), rel_iso hx x25 x26 -> rel_iso hx0 (x23 x25) (x24 x26)) -> forall (x25 : x1) (x26 : x2), rel_iso hx x25 x26 -> rel_iso hx2 (x21 x23 x25) (x22 x24 x26)) ->
  forall (x23 : x9) (x24 : x10),
  rel_iso hx3 x23 x24 ->
  forall (x25 : x1) (x26 : x2),
  rel_iso hx x25 x26 ->
  rel_iso hx4 (Original.LF_DOT_AltAuto.LF.AltAuto.auto_example_2 x1 x3 x5 x7 x9 x11 x13 x15 x17 x19 x21 x23 x25)
    (imported_Original_LF__DOT__AltAuto_LF_AltAuto_auto__example__2 x14 x16 x18 x20 x22 x24 x26).
Existing Instance Original_LF__DOT__AltAuto_LF_AltAuto_auto__example__2_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.auto_example_2 ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_auto__example__2_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.auto_example_2 imported_Original_LF__DOT__AltAuto_LF_AltAuto_auto__example__2 ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_auto__example__2_iso; constructor : typeclass_instances.


End Interface.