From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_nat__mul__iso Interface.__0__iso Interface.or__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_nat__mul__iso Interface.__0__iso Interface.or__iso.

  Export Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_nat__mul__iso.CodeBlocks Interface.__0__iso.CodeBlocks Interface.or__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_nat__mul__iso.Interface <+ Interface.__0__iso.Interface <+ Interface.or__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_factor__is__O : forall x x0 : imported_nat,
  imported_or (imported_Corelib_Init_Logic_eq x imported_0) (imported_Corelib_Init_Logic_eq x0 imported_0) -> imported_Corelib_Init_Logic_eq (imported_Nat_mul x x0) imported_0.
Parameter Original_LF__DOT__Logic_LF_Logic_factor__is__O_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) (x5 : x1 = 0 \/ x3 = 0)
    (x6 : imported_or (imported_Corelib_Init_Logic_eq x2 imported_0) (imported_Corelib_Init_Logic_eq x4 imported_0)),
  rel_iso (relax_Iso_Ts_Ps (or_iso (Corelib_Init_Logic_eq_iso hx _0_iso) (Corelib_Init_Logic_eq_iso hx0 _0_iso))) x5 x6 ->
  rel_iso (relax_Iso_Ts_Ps (Corelib_Init_Logic_eq_iso (Nat_mul_iso hx hx0) _0_iso)) (Original.LF_DOT_Logic.LF.Logic.factor_is_O x1 x3 x5) (imported_Original_LF__DOT__Logic_LF_Logic_factor__is__O x6).
Existing Instance Original_LF__DOT__Logic_LF_Logic_factor__is__O_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.factor_is_O ?x) => unify x Original_LF__DOT__Logic_LF_Logic_factor__is__O_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.factor_is_O imported_Original_LF__DOT__Logic_LF_Logic_factor__is__O ?x) => unify x Original_LF__DOT__Logic_LF_Logic_factor__is__O_iso; constructor : typeclass_instances.


End Interface.