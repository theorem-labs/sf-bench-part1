From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_false__iso Interface.U_logic__not__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_false__iso Interface.U_logic__not__iso.

  Export Interface.U_false__iso.CodeBlocks Interface.U_logic__not__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_false__iso.Interface <+ Interface.U_logic__not__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_contrapositive : forall x x0 : SProp, (x -> x0) -> (x0 -> imported_False) -> x -> imported_False.
Parameter Original_LF__DOT__Logic_LF_Logic_contrapositive_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : Prop) (x4 : SProp) (hx0 : Iso x3 x4) (x5 : x1 -> x3) (x6 : x2 -> x4),
  (forall (x7 : x1) (x8 : x2), rel_iso hx x7 x8 -> rel_iso hx0 (x5 x7) (x6 x8)) ->
  forall (x7 : ~ x3) (x8 : x4 -> imported_False),
  (forall (x9 : x3) (x10 : x4), rel_iso hx0 x9 x10 -> rel_iso False_iso (x7 x9) (x8 x10)) ->
  forall (x9 : x1) (x10 : x2),
  rel_iso hx x9 x10 -> rel_iso False_iso (Original.LF_DOT_Logic.LF.Logic.contrapositive x1 x3 x5 x7 x9) (imported_Original_LF__DOT__Logic_LF_Logic_contrapositive x6 x8 x10).
Existing Instance Original_LF__DOT__Logic_LF_Logic_contrapositive_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.contrapositive ?x) => unify x Original_LF__DOT__Logic_LF_Logic_contrapositive_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.contrapositive imported_Original_LF__DOT__Logic_LF_Logic_contrapositive ?x) => unify x Original_LF__DOT__Logic_LF_Logic_contrapositive_iso; constructor : typeclass_instances.


End Interface.