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

Parameter imported_Original_LF__DOT__AltAuto_LF_AltAuto_eq__example1' : forall (x x0 x1 : Type) (x2 : x -> x0) (x3 : x0 -> x1) (x4 : x) (x5 : x0), imported_Corelib_Init_Logic_eq x5 (x2 x4) -> imported_Corelib_Init_Logic_eq (x3 x5) (x3 (x2 x4)).
Parameter Original_LF__DOT__AltAuto_LF_AltAuto_eq__example1'_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 x4 : Type) (hx0 : Iso x3 x4) (x5 x6 : Type) (hx1 : Iso x5 x6) (x7 : x1 -> x3) (x8 : x2 -> x4)
    (hx2 : forall (x9 : x1) (x10 : x2), rel_iso hx x9 x10 -> rel_iso hx0 (x7 x9) (x8 x10)) (x9 : x3 -> x5) (x10 : x4 -> x6)
    (hx3 : forall (x11 : x3) (x12 : x4), rel_iso hx0 x11 x12 -> rel_iso hx1 (x9 x11) (x10 x12)) (x11 : x1) (x12 : x2) (hx4 : rel_iso hx x11 x12) (x13 : x3) (x14 : x4) (hx5 : rel_iso hx0 x13 x14)
    (x15 : x13 = x7 x11) (x16 : imported_Corelib_Init_Logic_eq x14 (x8 x12)),
  rel_iso (Corelib_Init_Logic_eq_iso hx5 (hx2 x11 x12 hx4)) x15 x16 ->
  rel_iso (Corelib_Init_Logic_eq_iso (hx3 x13 x14 hx5) (hx3 (x7 x11) (x8 x12) (hx2 x11 x12 hx4))) (Original.LF_DOT_AltAuto.LF.AltAuto.eq_example1' x1 x3 x5 x7 x9 x11 x13 x15)
    (imported_Original_LF__DOT__AltAuto_LF_AltAuto_eq__example1' x8 x10 x12 x16).
Existing Instance Original_LF__DOT__AltAuto_LF_AltAuto_eq__example1'_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.eq_example1' ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_eq__example1'_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.eq_example1' imported_Original_LF__DOT__AltAuto_LF_AltAuto_eq__example1' ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_eq__example1'_iso; constructor : typeclass_instances.


End Interface.