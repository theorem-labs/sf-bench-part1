From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.or__iso.

Module Export CodeBlocks.

  Export (hints) Interface.or__iso.

  Export Interface.or__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.or__iso.Args <+ Interface.or__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_or__commut : forall x x0 : SProp, imported_or x x0 -> imported_or x0 x.
Parameter Original_LF__DOT__Logic_LF_Logic_or__commut_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : Prop) (x4 : SProp) (hx0 : Iso x3 x4) (x5 : x1 \/ x3) (x6 : imported_or x2 x4),
  rel_iso (or_iso hx hx0) x5 x6 -> rel_iso (or_iso hx0 hx) (Original.LF_DOT_Logic.LF.Logic.or_commut x1 x3 x5) (imported_Original_LF__DOT__Logic_LF_Logic_or__commut x6).
Existing Instance Original_LF__DOT__Logic_LF_Logic_or__commut_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.or_commut ?x) => unify x Original_LF__DOT__Logic_LF_Logic_or__commut_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.or_commut imported_Original_LF__DOT__Logic_LF_Logic_or__commut ?x) => unify x Original_LF__DOT__Logic_LF_Logic_or__commut_iso; constructor : typeclass_instances.


End Interface.