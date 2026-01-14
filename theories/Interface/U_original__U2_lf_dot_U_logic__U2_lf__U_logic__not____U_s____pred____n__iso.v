From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_false__iso Interface.U_logic__not__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_nat__pred__iso Interface.U_s__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_false__iso Interface.U_logic__not__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_nat__pred__iso Interface.U_s__iso.

  Export Interface.U_false__iso.CodeBlocks Interface.U_logic__not__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_nat__pred__iso.CodeBlocks Interface.U_s__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_false__iso.Interface <+ Interface.U_logic__not__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_nat__pred__iso.Interface <+ Interface.U_s__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_not__S__pred__n : (forall x : imported_nat, imported_Corelib_Init_Logic_eq (imported_S (imported_Nat_pred x)) x) -> imported_False.
Parameter Original_LF__DOT__Logic_LF_Logic_not__S__pred__n_iso : forall (x1 : forall n : nat, S (Nat.pred n) = n) (x2 : forall x : imported_nat, imported_Corelib_Init_Logic_eq (imported_S (imported_Nat_pred x)) x),
  (forall (x3 : nat) (x4 : imported_nat) (hx : rel_iso nat_iso x3 x4), rel_iso (Corelib_Init_Logic_eq_iso (S_iso (Nat_pred_iso hx)) hx) (x1 x3) (x2 x4)) ->
  rel_iso False_iso (Original.LF_DOT_Logic.LF.Logic.not_S_pred_n x1) (imported_Original_LF__DOT__Logic_LF_Logic_not__S__pred__n x2).
Existing Instance Original_LF__DOT__Logic_LF_Logic_not__S__pred__n_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.not_S_pred_n ?x) => unify x Original_LF__DOT__Logic_LF_Logic_not__S__pred__n_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.not_S_pred_n imported_Original_LF__DOT__Logic_LF_Logic_not__S__pred__n ?x) => unify x Original_LF__DOT__Logic_LF_Logic_not__S__pred__n_iso; constructor : typeclass_instances.


End Interface.