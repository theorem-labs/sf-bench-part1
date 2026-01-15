From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.and__iso Interface.or__iso.

Module Export CodeBlocks.

  Export (hints) Interface.and__iso Interface.or__iso.

  Export Interface.and__iso.CodeBlocks Interface.or__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.and__iso.Interface <+ Interface.or__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Auto_LF_Auto_auto__example__4 : forall x x0 x1 : SProp, x0 -> (x0 -> x1) -> imported_or x (imported_and x0 x1).
Parameter Original_LF__DOT__Auto_LF_Auto_auto__example__4_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : Prop) (x4 : SProp) (hx0 : Iso x3 x4) (x5 : Prop) (x6 : SProp) (hx1 : Iso x5 x6) (x7 : x3) (x8 : x4),
  rel_iso hx0 x7 x8 ->
  forall (x9 : x3 -> x5) (x10 : x4 -> x6),
  (forall (x11 : x3) (x12 : x4), rel_iso hx0 x11 x12 -> rel_iso hx1 (x9 x11) (x10 x12)) ->
  rel_iso (relax_Iso_Ts_Ps (or_iso hx (and_iso hx0 hx1))) (Original.LF_DOT_Auto.LF.Auto.auto_example_4 x1 x3 x5 x7 x9) (imported_Original_LF__DOT__Auto_LF_Auto_auto__example__4 x2 x8 x10).
Existing Instance Original_LF__DOT__Auto_LF_Auto_auto__example__4_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Auto.LF.Auto.auto_example_4 ?x) => unify x Original_LF__DOT__Auto_LF_Auto_auto__example__4_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Auto.LF.Auto.auto_example_4 imported_Original_LF__DOT__Auto_LF_Auto_auto__example__4 ?x) => unify x Original_LF__DOT__Auto_LF_Auto_auto__example__4_iso; constructor : typeclass_instances.


End Interface.