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

Parameter imported_Original_LF__DOT__Logic_LF_Logic_not__implies__our__not : forall x : SProp, (x -> imported_False) -> forall x1 : SProp, x -> x1.
Parameter Original_LF__DOT__Logic_LF_Logic_not__implies__our__not_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : ~ x1) (x4 : x2 -> imported_False),
  (forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> rel_iso False_iso (x3 x5) (x4 x6)) ->
  forall (x5 : Prop) (x6 : SProp) (hx1 : Iso x5 x6) (x7 : x1) (x8 : x2),
  rel_iso hx x7 x8 -> rel_iso hx1 (Original.LF_DOT_Logic.LF.Logic.not_implies_our_not x1 x3 x5 x7) (imported_Original_LF__DOT__Logic_LF_Logic_not__implies__our__not x4 x6 x8).
Existing Instance Original_LF__DOT__Logic_LF_Logic_not__implies__our__not_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.not_implies_our_not ?x) => unify x Original_LF__DOT__Logic_LF_Logic_not__implies__our__not_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.not_implies_our_not imported_Original_LF__DOT__Logic_LF_Logic_not__implies__our__not ?x) => unify x Original_LF__DOT__Logic_LF_Logic_not__implies__our__not_iso; constructor : typeclass_instances.


End Interface.