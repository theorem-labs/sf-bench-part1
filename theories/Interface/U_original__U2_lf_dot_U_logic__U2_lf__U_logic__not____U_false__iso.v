From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_false__iso Interface.U_logic__not__iso Interface.U_original__U_false__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_false__iso Interface.U_logic__not__iso Interface.U_original__U_false__iso.

  Export Interface.U_false__iso.CodeBlocks Interface.U_logic__not__iso.CodeBlocks Interface.U_original__U_false__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_false__iso.Interface <+ Interface.U_logic__not__iso.Interface <+ Interface.U_original__U_false__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_not__False : imported_Original_False -> imported_False.
Parameter Original_LF__DOT__Logic_LF_Logic_not__False_iso : forall (x1 : Original.False) (x2 : imported_Original_False),
  rel_iso Original_False_iso x1 x2 -> rel_iso False_iso (Original.LF_DOT_Logic.LF.Logic.not_False x1) (imported_Original_LF__DOT__Logic_LF_Logic_not__False x2).
Existing Instance Original_LF__DOT__Logic_LF_Logic_not__False_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.not_False ?x) => unify x Original_LF__DOT__Logic_LF_Logic_not__False_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.not_False imported_Original_LF__DOT__Logic_LF_Logic_not__False ?x) => unify x Original_LF__DOT__Logic_LF_Logic_not__False_iso; constructor : typeclass_instances.


End Interface.