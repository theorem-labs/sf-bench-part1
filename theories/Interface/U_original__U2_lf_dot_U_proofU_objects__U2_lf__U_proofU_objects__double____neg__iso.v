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

Parameter imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_double__neg : forall x : SProp, x -> (x -> imported_False) -> imported_False.
Parameter Original_LF__DOT__ProofObjects_LF_ProofObjects_double__neg_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2),
  rel_iso hx x3 x4 ->
  forall (x5 : x1 -> False) (x6 : x2 -> imported_False),
  (forall (x7 : x1) (x8 : x2), rel_iso hx x7 x8 -> rel_iso False_iso (x5 x7) (x6 x8)) ->
  rel_iso False_iso (Original.LF_DOT_ProofObjects.LF.ProofObjects.double_neg x1 x3 x5) (imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_double__neg x4 x6).
Existing Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_double__neg_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.double_neg ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_double__neg_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.double_neg imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_double__neg ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_double__neg_iso; constructor : typeclass_instances.


End Interface.