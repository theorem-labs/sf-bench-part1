From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.iff__iso.

Module Export CodeBlocks.

  Export (hints) Interface.iff__iso.

  Export Interface.iff__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.iff__iso.Args <+ Interface.iff__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_apply__iff__example1 : forall x x0 x1 : SProp, imported_iff x x0 -> (x0 -> x1) -> x -> x1.
Parameter Original_LF__DOT__Logic_LF_Logic_apply__iff__example1_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : Prop) (x4 : SProp) (hx0 : Iso x3 x4) (x5 : Prop) (x6 : SProp) (hx1 : Iso x5 x6) (x7 : x1 <-> x3) (x8 : imported_iff x2 x4),
  rel_iso (iff_iso hx hx0) x7 x8 ->
  forall (x9 : x3 -> x5) (x10 : x4 -> x6),
  (forall (x11 : x3) (x12 : x4), rel_iso hx0 x11 x12 -> rel_iso hx1 (x9 x11) (x10 x12)) ->
  forall (x11 : x1) (x12 : x2),
  rel_iso hx x11 x12 -> rel_iso hx1 (Original.LF_DOT_Logic.LF.Logic.apply_iff_example1 x1 x3 x5 x7 x9 x11) (imported_Original_LF__DOT__Logic_LF_Logic_apply__iff__example1 x8 x10 x12).
Existing Instance Original_LF__DOT__Logic_LF_Logic_apply__iff__example1_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.apply_iff_example1 ?x) => unify x Original_LF__DOT__Logic_LF_Logic_apply__iff__example1_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.apply_iff_example1 imported_Original_LF__DOT__Logic_LF_Logic_apply__iff__example1 ?x) => unify x Original_LF__DOT__Logic_LF_Logic_apply__iff__example1_iso; constructor : typeclass_instances.


End Interface.