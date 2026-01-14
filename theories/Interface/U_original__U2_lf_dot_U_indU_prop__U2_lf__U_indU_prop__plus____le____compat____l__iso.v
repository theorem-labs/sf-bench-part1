From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.nat__iso Interface.U_nat__add__iso Interface.le__iso.

Module Export CodeBlocks.

  Export (hints) Interface.nat__iso Interface.U_nat__add__iso Interface.le__iso.

  Export Interface.nat__iso.CodeBlocks Interface.U_nat__add__iso.CodeBlocks Interface.le__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.nat__iso.Interface <+ Interface.U_nat__add__iso.Interface <+ Interface.le__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_plus__le__compat__l : forall x x0 x1 : imported_nat, imported_le x x0 -> imported_le (imported_Nat_add x1 x) (imported_Nat_add x1 x0).
Parameter Original_LF__DOT__IndProp_LF_IndProp_plus__le__compat__l_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) (x5 : nat) (x6 : imported_nat) (hx1 : rel_iso nat_iso x5 x6)
    (x7 : x1 <= x3) (x8 : imported_le x2 x4),
  rel_iso (le_iso hx hx0) x7 x8 ->
  rel_iso (le_iso (Nat_add_iso hx1 hx) (Nat_add_iso hx1 hx0)) (Original.LF_DOT_IndProp.LF.IndProp.plus_le_compat_l x1 x3 x5 x7)
    (imported_Original_LF__DOT__IndProp_LF_IndProp_plus__le__compat__l x6 x8).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_plus__le__compat__l_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.plus_le_compat_l ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_plus__le__compat__l_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.plus_le_compat_l imported_Original_LF__DOT__IndProp_LF_IndProp_plus__le__compat__l ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_plus__le__compat__l_iso; constructor : typeclass_instances.


End Interface.