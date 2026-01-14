From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso.

  Export Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Lists_LF_Lists_NatList_involution__injective : forall x : imported_nat -> imported_nat,
  (forall x0 : imported_nat, imported_Corelib_Init_Logic_eq x0 (x (x x0))) -> forall x1 x2 : imported_nat, imported_Corelib_Init_Logic_eq (x x1) (x x2) -> imported_Corelib_Init_Logic_eq x1 x2.
Parameter Original_LF__DOT__Lists_LF_Lists_NatList_involution__injective_iso : forall (x1 : nat -> nat) (x2 : imported_nat -> imported_nat) (hx : forall (x3 : nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> rel_iso nat_iso (x1 x3) (x2 x4))
    (x3 : forall n : nat, n = x1 (x1 n)) (x4 : forall x : imported_nat, imported_Corelib_Init_Logic_eq x (x2 (x2 x))),
  (forall (x5 : nat) (x6 : imported_nat) (hx0 : rel_iso nat_iso x5 x6), rel_iso (Corelib_Init_Logic_eq_iso hx0 (hx (x1 x5) (x2 x6) (hx x5 x6 hx0))) (x3 x5) (x4 x6)) ->
  forall (x5 : nat) (x6 : imported_nat) (hx1 : rel_iso nat_iso x5 x6) (x7 : nat) (x8 : imported_nat) (hx2 : rel_iso nat_iso x7 x8) (x9 : x1 x5 = x1 x7)
    (x10 : imported_Corelib_Init_Logic_eq (x2 x6) (x2 x8)),
  rel_iso (Corelib_Init_Logic_eq_iso (hx x5 x6 hx1) (hx x7 x8 hx2)) x9 x10 ->
  rel_iso (Corelib_Init_Logic_eq_iso hx1 hx2) (Original.LF_DOT_Lists.LF.Lists.NatList.involution_injective x1 x3 x5 x7 x9)
    (imported_Original_LF__DOT__Lists_LF_Lists_NatList_involution__injective x2 x4 x6 x8 x10).
Existing Instance Original_LF__DOT__Lists_LF_Lists_NatList_involution__injective_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.NatList.involution_injective ?x) => unify x Original_LF__DOT__Lists_LF_Lists_NatList_involution__injective_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.NatList.involution_injective imported_Original_LF__DOT__Lists_LF_Lists_NatList_involution__injective ?x) => unify x Original_LF__DOT__Lists_LF_Lists_NatList_involution__injective_iso; constructor : typeclass_instances.


End Interface.