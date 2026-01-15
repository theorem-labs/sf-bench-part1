From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_false__iso Interface.U_logic__not__iso Interface.and__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_false__iso Interface.U_logic__not__iso Interface.and__iso.

  Export Interface.U_false__iso.CodeBlocks Interface.U_logic__not__iso.CodeBlocks Interface.and__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_false__iso.Interface <+ Interface.U_logic__not__iso.Interface <+ Interface.and__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_contradiction__implies__anything : forall x x0 : SProp, imported_and x (x -> imported_False) -> x0.
Parameter Original_LF__DOT__Logic_LF_Logic_contradiction__implies__anything_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : Prop) (x4 : SProp) (hx0 : Iso x3 x4) (x5 : x1 /\ ~ x1) (x6 : imported_and x2 (x2 -> imported_False)),
  rel_iso (relax_Iso_Ts_Ps (and_iso hx (IsoArrow hx False_iso))) x5 x6 ->
  rel_iso hx0 (Original.LF_DOT_Logic.LF.Logic.contradiction_implies_anything x1 x3 x5) (imported_Original_LF__DOT__Logic_LF_Logic_contradiction__implies__anything x4 x6).
Existing Instance Original_LF__DOT__Logic_LF_Logic_contradiction__implies__anything_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.contradiction_implies_anything ?x) => unify x Original_LF__DOT__Logic_LF_Logic_contradiction__implies__anything_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.contradiction_implies_anything imported_Original_LF__DOT__Logic_LF_Logic_contradiction__implies__anything ?x) => unify x Original_LF__DOT__Logic_LF_Logic_contradiction__implies__anything_iso; constructor : typeclass_instances.


End Interface.