From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.nat__iso Interface.U_nat__add__iso Interface.le__iso Interface.or__iso.

Module Export CodeBlocks.

  Export (hints) Interface.nat__iso Interface.U_nat__add__iso Interface.le__iso Interface.or__iso.

  Export Interface.nat__iso.CodeBlocks Interface.U_nat__add__iso.CodeBlocks Interface.le__iso.CodeBlocks Interface.or__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.nat__iso.Interface <+ Interface.U_nat__add__iso.Interface <+ Interface.le__iso.Interface <+ Interface.or__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_plus__le__cases : forall x x0 x1 x2 : imported_nat, imported_le (imported_Nat_add x x0) (imported_Nat_add x1 x2) -> imported_or (imported_le x x1) (imported_le x0 x2).
Parameter Original_LF__DOT__IndProp_LF_IndProp_plus__le__cases_iso : forall (x1 : nat) (x2 : imported_nat) (hx : @rel_iso nat imported_nat nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : @rel_iso nat imported_nat nat_iso x3 x4) (x5 : nat) 
    (x6 : imported_nat) (hx1 : @rel_iso nat imported_nat nat_iso x5 x6) (x7 : nat) (x8 : imported_nat) (hx2 : @rel_iso nat imported_nat nat_iso x7 x8) (x9 : x1 + x3 <= x5 + x7)
    (x10 : imported_le (imported_Nat_add x2 x4) (imported_Nat_add x6 x8)),
  @rel_iso (x1 + x3 <= x5 + x7) (imported_le (imported_Nat_add x2 x4) (imported_Nat_add x6 x8))
    (@relax_Iso_Ts_Ps (x1 + x3 <= x5 + x7) (imported_le (imported_Nat_add x2 x4) (imported_Nat_add x6 x8))
       (@le_iso (x1 + x3) (imported_Nat_add x2 x4) (@Nat_add_iso x1 x2 hx x3 x4 hx0) (x5 + x7) (imported_Nat_add x6 x8) (@Nat_add_iso x5 x6 hx1 x7 x8 hx2)))
    x9 x10 ->
  @rel_iso (x1 <= x5 \/ x3 <= x7) (imported_or (imported_le x2 x6) (imported_le x4 x8))
    (@relax_Iso_Ts_Ps (x1 <= x5 \/ x3 <= x7) (imported_or (imported_le x2 x6) (imported_le x4 x8))
       (@or_iso (x1 <= x5) (imported_le x2 x6) (@le_iso x1 x2 hx x5 x6 hx1) (x3 <= x7) (imported_le x4 x8) (@le_iso x3 x4 hx0 x7 x8 hx2)))
    (Original.LF_DOT_IndProp.LF.IndProp.plus_le_cases x1 x3 x5 x7 x9) (@imported_Original_LF__DOT__IndProp_LF_IndProp_plus__le__cases x2 x4 x6 x8 x10).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_plus__le__cases_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.plus_le_cases ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_plus__le__cases_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.plus_le_cases imported_Original_LF__DOT__IndProp_LF_IndProp_plus__le__cases ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_plus__le__cases_iso; constructor : typeclass_instances.


End Interface.