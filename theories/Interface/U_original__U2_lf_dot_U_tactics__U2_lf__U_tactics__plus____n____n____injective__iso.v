From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_nat__add__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_nat__add__iso.

  Export Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_nat__add__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_nat__add__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Tactics_LF_Tactics_plus__n__n__injective : forall x x0 : imported_nat, imported_Corelib_Init_Logic_eq (imported_Nat_add x x) (imported_Nat_add x0 x0) -> imported_Corelib_Init_Logic_eq x x0.
Parameter Original_LF__DOT__Tactics_LF_Tactics_plus__n__n__injective_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) (x5 : x1 + x1 = x3 + x3)
    (x6 : imported_Corelib_Init_Logic_eq (imported_Nat_add x2 x2) (imported_Nat_add x4 x4)),
  rel_iso (Corelib_Init_Logic_eq_iso (Nat_add_iso hx hx) (Nat_add_iso hx0 hx0)) x5 x6 ->
  rel_iso (Corelib_Init_Logic_eq_iso hx hx0) (Original.LF_DOT_Tactics.LF.Tactics.plus_n_n_injective x1 x3 x5) (imported_Original_LF__DOT__Tactics_LF_Tactics_plus__n__n__injective x6).
Existing Instance Original_LF__DOT__Tactics_LF_Tactics_plus__n__n__injective_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Tactics.LF.Tactics.plus_n_n_injective ?x) => unify x Original_LF__DOT__Tactics_LF_Tactics_plus__n__n__injective_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Tactics.LF.Tactics.plus_n_n_injective imported_Original_LF__DOT__Tactics_LF_Tactics_plus__n__n__injective ?x) => unify x Original_LF__DOT__Tactics_LF_Tactics_plus__n__n__injective_iso; constructor : typeclass_instances.


End Interface.