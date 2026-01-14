From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.and__iso.

Module Export CodeBlocks.

  Export (hints) Interface.and__iso.

  Export Interface.and__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.and__iso.Args <+ Interface.and__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_uncurry : forall x x0 x1 : SProp, (x -> x0 -> x1) -> imported_and x x0 -> x1.
Parameter Original_LF__DOT__ProofObjects_LF_ProofObjects_uncurry_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : Prop) (x4 : SProp) (hx0 : Iso x3 x4) (x5 : Prop) (x6 : SProp) (hx1 : Iso x5 x6) (x7 : x1 -> x3 -> x5) (x8 : x2 -> x4 -> x6),
  (forall (x9 : x1) (x10 : x2), rel_iso hx x9 x10 -> forall (x11 : x3) (x12 : x4), rel_iso hx0 x11 x12 -> rel_iso hx1 (x7 x9 x11) (x8 x10 x12)) ->
  forall (x9 : x1 /\ x3) (x10 : imported_and x2 x4),
  rel_iso (and_iso hx hx0) x9 x10 -> rel_iso hx1 (Original.LF_DOT_ProofObjects.LF.ProofObjects.uncurry x1 x3 x5 x7 x9) (imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_uncurry x8 x10).
Existing Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_uncurry_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.uncurry ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_uncurry_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.uncurry imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_uncurry ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_uncurry_iso; constructor : typeclass_instances.


End Interface.