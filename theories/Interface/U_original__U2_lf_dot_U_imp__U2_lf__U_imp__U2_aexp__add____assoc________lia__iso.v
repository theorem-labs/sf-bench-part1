From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_peanoU_nat__U_nat__add__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_peanoU_nat__U_nat__add__iso.

  Export Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_peanoU_nat__U_nat__add__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_peanoU_nat__U_nat__add__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Imp_LF_Imp_AExp_add__assoc____lia : forall x x0 x1 : imported_nat, imported_Corelib_Init_Logic_eq (imported_PeanoNat_Nat_add x (imported_PeanoNat_Nat_add x0 x1)) (imported_PeanoNat_Nat_add (imported_PeanoNat_Nat_add x x0) x1).
Parameter Original_LF__DOT__Imp_LF_Imp_AExp_add__assoc____lia_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) (x5 : nat) (x6 : imported_nat) (hx1 : rel_iso nat_iso x5 x6),
  rel_iso (Corelib_Init_Logic_eq_iso (PeanoNat_Nat_add_iso hx (PeanoNat_Nat_add_iso hx0 hx1)) (PeanoNat_Nat_add_iso (PeanoNat_Nat_add_iso hx hx0) hx1))
    (Original.LF_DOT_Imp.LF.Imp.AExp.add_assoc__lia x1 x3 x5) (imported_Original_LF__DOT__Imp_LF_Imp_AExp_add__assoc____lia x2 x4 x6).
Existing Instance Original_LF__DOT__Imp_LF_Imp_AExp_add__assoc____lia_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.AExp.add_assoc__lia ?x) => unify x Original_LF__DOT__Imp_LF_Imp_AExp_add__assoc____lia_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.AExp.add_assoc__lia imported_Original_LF__DOT__Imp_LF_Imp_AExp_add__assoc____lia ?x) => unify x Original_LF__DOT__Imp_LF_Imp_AExp_add__assoc____lia_iso; constructor : typeclass_instances.


End Interface.