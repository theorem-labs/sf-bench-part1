From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.nat__iso Interface.U_peanoU_nat__U_nat__leb__iso Interface.__0__iso Interface.true__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.nat__iso Interface.U_peanoU_nat__U_nat__leb__iso Interface.__0__iso Interface.true__iso.

  Export Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.bool__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_peanoU_nat__U_nat__leb__iso.CodeBlocks Interface.__0__iso.CodeBlocks Interface.true__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.bool__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_peanoU_nat__U_nat__leb__iso.Interface <+ Interface.__0__iso.Interface <+ Interface.true__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Imp_LF_Imp_AExp_foo' : forall x : imported_nat, imported_Corelib_Init_Logic_eq (imported_PeanoNat_Nat_leb imported_0 x) imported_true.
Parameter Original_LF__DOT__Imp_LF_Imp_AExp_foo'_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2),
  rel_iso (Corelib_Init_Logic_eq_iso (PeanoNat_Nat_leb_iso _0_iso hx) true_iso) (Original.LF_DOT_Imp.LF.Imp.AExp.foo' x1) (imported_Original_LF__DOT__Imp_LF_Imp_AExp_foo' x2).
Existing Instance Original_LF__DOT__Imp_LF_Imp_AExp_foo'_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.AExp.foo' ?x) => unify x Original_LF__DOT__Imp_LF_Imp_AExp_foo'_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.AExp.foo' imported_Original_LF__DOT__Imp_LF_Imp_AExp_foo' ?x) => unify x Original_LF__DOT__Imp_LF_Imp_AExp_foo'_iso; constructor : typeclass_instances.


End Interface.