From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.and__iso Interface.nat__iso Interface.U_nat__add__iso Interface.le__iso.

Module Export CodeBlocks.

  Export (hints) Interface.and__iso Interface.nat__iso Interface.U_nat__add__iso Interface.le__iso.

  Export Interface.and__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_nat__add__iso.CodeBlocks Interface.le__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.and__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_nat__add__iso.Interface <+ Interface.le__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_plus__le : forall x x0 x1 : imported_nat, imported_le (imported_Nat_add x x0) x1 -> imported_and (imported_le x x1) (imported_le x0 x1).
Parameter Original_LF__DOT__IndProp_LF_IndProp_plus__le_iso : forall (x1 : nat) (x2 : imported_nat) (hx : @rel_iso nat imported_nat nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : @rel_iso nat imported_nat nat_iso x3 x4) (x5 : nat) 
    (x6 : imported_nat) (hx1 : @rel_iso nat imported_nat nat_iso x5 x6) (x7 : x1 + x3 <= x5) (x8 : imported_le (imported_Nat_add x2 x4) x6),
  @rel_iso (x1 + x3 <= x5) (imported_le (imported_Nat_add x2 x4) x6)
    (@relax_Iso_Ts_Ps (x1 + x3 <= x5) (imported_le (imported_Nat_add x2 x4) x6) (@le_iso (x1 + x3) (imported_Nat_add x2 x4) (@Nat_add_iso x1 x2 hx x3 x4 hx0) x5 x6 hx1)) x7 x8 ->
  @rel_iso (x1 <= x5 /\ x3 <= x5) (imported_and (imported_le x2 x6) (imported_le x4 x6))
    (@relax_Iso_Ts_Ps (x1 <= x5 /\ x3 <= x5) (imported_and (imported_le x2 x6) (imported_le x4 x6))
       (@and_iso (x1 <= x5) (imported_le x2 x6) (@le_iso x1 x2 hx x5 x6 hx1) (x3 <= x5) (imported_le x4 x6) (@le_iso x3 x4 hx0 x5 x6 hx1)))
    (Original.LF_DOT_IndProp.LF.IndProp.plus_le x1 x3 x5 x7) (@imported_Original_LF__DOT__IndProp_LF_IndProp_plus__le x2 x4 x6 x8).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_plus__le_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.plus_le ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_plus__le_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.plus_le imported_Original_LF__DOT__IndProp_LF_IndProp_plus__le ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_plus__le_iso; constructor : typeclass_instances.


End Interface.