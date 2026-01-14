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

Parameter imported_Original_LF__DOT__Tactics_LF_Tactics_f__equal : forall (x x0 : Type) (x1 : x -> x0) (x2 x3 : x), imported_Corelib_Init_Logic_eq x2 x3 -> imported_Corelib_Init_Logic_eq (x1 x2) (x1 x3).
Parameter Original_LF__DOT__Tactics_LF_Tactics_f__equal_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 x4 : Type) (hx0 : Iso x3 x4) (x5 : x1 -> x3) (x6 : x2 -> x4) (hx1 : forall (x7 : x1) (x8 : x2), rel_iso hx x7 x8 -> rel_iso hx0 (x5 x7) (x6 x8)) 
    (x7 : x1) (x8 : x2) (hx2 : rel_iso hx x7 x8) (x9 : x1) (x10 : x2) (hx3 : rel_iso hx x9 x10) (x11 : x7 = x9) (x12 : imported_Corelib_Init_Logic_eq x8 x10),
  rel_iso (Corelib_Init_Logic_eq_iso hx2 hx3) x11 x12 ->
  rel_iso (Corelib_Init_Logic_eq_iso (hx1 x7 x8 hx2) (hx1 x9 x10 hx3)) (Original.LF_DOT_Tactics.LF.Tactics.f_equal x1 x3 x5 x7 x9 x11) (imported_Original_LF__DOT__Tactics_LF_Tactics_f__equal x6 x12).
Existing Instance Original_LF__DOT__Tactics_LF_Tactics_f__equal_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Tactics.LF.Tactics.f_equal ?x) => unify x Original_LF__DOT__Tactics_LF_Tactics_f__equal_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Tactics.LF.Tactics.f_equal imported_Original_LF__DOT__Tactics_LF_Tactics_f__equal ?x) => unify x Original_LF__DOT__Tactics_LF_Tactics_f__equal_iso; constructor : typeclass_instances.


End Interface.