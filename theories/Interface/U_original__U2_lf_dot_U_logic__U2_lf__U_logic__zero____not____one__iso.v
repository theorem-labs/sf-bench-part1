From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_false__iso Interface.U_logic__not__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_s__iso Interface.__0__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_false__iso Interface.U_logic__not__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_s__iso Interface.__0__iso.

  Export Interface.U_false__iso.CodeBlocks Interface.U_logic__not__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_false__iso.Interface <+ Interface.U_logic__not__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_zero__not__one : imported_Corelib_Init_Logic_eq imported_0 (imported_S imported_0) -> imported_False.
Parameter Original_LF__DOT__Logic_LF_Logic_zero__not__one_iso : forall (x1 : 0 = 1) (x2 : imported_Corelib_Init_Logic_eq imported_0 (imported_S imported_0)),
  rel_iso (Corelib_Init_Logic_eq_iso _0_iso (S_iso _0_iso)) x1 x2 -> rel_iso False_iso (Original.LF_DOT_Logic.LF.Logic.zero_not_one x1) (imported_Original_LF__DOT__Logic_LF_Logic_zero__not__one x2).
Existing Instance Original_LF__DOT__Logic_LF_Logic_zero__not__one_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.zero_not_one ?x) => unify x Original_LF__DOT__Logic_LF_Logic_zero__not__one_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.zero_not_one imported_Original_LF__DOT__Logic_LF_Logic_zero__not__one ?x) => unify x Original_LF__DOT__Logic_LF_Logic_zero__not__one_iso; constructor : typeclass_instances.


End Interface.