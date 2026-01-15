From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.and__iso Interface.nat__iso Interface.le__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.and__iso Interface.nat__iso Interface.le__iso.

  Export Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.and__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.le__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.and__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.le__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Auto_LF_Auto_le__antisym : forall x x0 : imported_nat, imported_and (imported_le x x0) (imported_le x0 x) -> imported_Corelib_Init_Logic_eq x x0.
Parameter Original_LF__DOT__Auto_LF_Auto_le__antisym_iso : forall (x1 : nat) (x2 : imported_nat) (hx : @rel_iso nat imported_nat nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : @rel_iso nat imported_nat nat_iso x3 x4) (x5 : x1 <= x3 <= x1)
    (x6 : imported_and (imported_le x2 x4) (imported_le x4 x2)),
  @rel_iso (x1 <= x3 <= x1) (imported_and (imported_le x2 x4) (imported_le x4 x2))
    (@relax_Iso_Ts_Ps (x1 <= x3 <= x1) (imported_and (imported_le x2 x4) (imported_le x4 x2))
       (@and_iso (x1 <= x3) (imported_le x2 x4) (@le_iso x1 x2 hx x3 x4 hx0) (x3 <= x1) (imported_le x4 x2) (@le_iso x3 x4 hx0 x1 x2 hx)))
    x5 x6 ->
  @rel_iso (x1 = x3) (@imported_Corelib_Init_Logic_eq imported_nat x2 x4)
    (@relax_Iso_Ts_Ps (x1 = x3) (@imported_Corelib_Init_Logic_eq imported_nat x2 x4) (@Corelib_Init_Logic_eq_iso nat imported_nat nat_iso x1 x2 hx x3 x4 hx0))
    (Original.LF_DOT_Auto.LF.Auto.le_antisym x1 x3 x5) (@imported_Original_LF__DOT__Auto_LF_Auto_le__antisym x2 x4 x6).
Existing Instance Original_LF__DOT__Auto_LF_Auto_le__antisym_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Auto.LF.Auto.le_antisym ?x) => unify x Original_LF__DOT__Auto_LF_Auto_le__antisym_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Auto.LF.Auto.le_antisym imported_Original_LF__DOT__Auto_LF_Auto_le__antisym ?x) => unify x Original_LF__DOT__Auto_LF_Auto_le__antisym_iso; constructor : typeclass_instances.


End Interface.