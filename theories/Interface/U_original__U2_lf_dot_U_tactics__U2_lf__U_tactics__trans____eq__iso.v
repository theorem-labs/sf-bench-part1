From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso.

  Export Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Tactics_LF_Tactics_trans__eq : forall (x : Type) (x0 x1 x2 : x), imported_Corelib_Init_Logic_eq x0 x1 -> imported_Corelib_Init_Logic_eq x1 x2 -> imported_Corelib_Init_Logic_eq x0 x2.
Parameter Original_LF__DOT__Tactics_LF_Tactics_trans__eq_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (hx0 : rel_iso hx x3 x4) (x5 : x1) (x6 : x2) (hx1 : rel_iso hx x5 x6) (x7 : x1) (x8 : x2) (hx2 : rel_iso hx x7 x8) 
    (x9 : x3 = x5) (x10 : imported_Corelib_Init_Logic_eq x4 x6),
  rel_iso (Corelib_Init_Logic_eq_iso hx0 hx1) x9 x10 ->
  forall (x11 : x5 = x7) (x12 : imported_Corelib_Init_Logic_eq x6 x8),
  rel_iso (Corelib_Init_Logic_eq_iso hx1 hx2) x11 x12 ->
  rel_iso (Corelib_Init_Logic_eq_iso hx0 hx2) (Original.LF_DOT_Tactics.LF.Tactics.trans_eq x1 x3 x5 x7 x9 x11) (imported_Original_LF__DOT__Tactics_LF_Tactics_trans__eq x10 x12).
Existing Instance Original_LF__DOT__Tactics_LF_Tactics_trans__eq_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Tactics.LF.Tactics.trans_eq ?x) => unify x Original_LF__DOT__Tactics_LF_Tactics_trans__eq_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Tactics.LF.Tactics.trans_eq imported_Original_LF__DOT__Tactics_LF_Tactics_trans__eq ?x) => unify x Original_LF__DOT__Tactics_LF_Tactics_trans__eq_iso; constructor : typeclass_instances.


End Interface.