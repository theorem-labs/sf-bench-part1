From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.nat__iso Interface.U_nat__add__iso Interface.U_nat__mul__iso Interface.le__iso.

Module Export CodeBlocks.

  Export (hints) Interface.nat__iso Interface.U_nat__add__iso Interface.U_nat__mul__iso Interface.le__iso.

  Export Interface.nat__iso.CodeBlocks Interface.U_nat__add__iso.CodeBlocks Interface.U_nat__mul__iso.CodeBlocks Interface.le__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.nat__iso.Interface <+ Interface.U_nat__add__iso.Interface <+ Interface.U_nat__mul__iso.Interface <+ Interface.le__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__AltAuto_LF_AltAuto_trans__example2 : forall x x0 x1 x2 : imported_nat, imported_le x (imported_Nat_add x0 (imported_Nat_mul x0 x1)) -> imported_le (imported_Nat_add x0 (imported_Nat_mul x0 x1)) x2 -> imported_le x x2.
Parameter Original_LF__DOT__AltAuto_LF_AltAuto_trans__example2_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) (x5 : nat) (x6 : imported_nat) (hx1 : rel_iso nat_iso x5 x6)
    (x7 : nat) (x8 : imported_nat) (hx2 : rel_iso nat_iso x7 x8) (x9 : x1 <= x3 + x3 * x5) (x10 : imported_le x2 (imported_Nat_add x4 (imported_Nat_mul x4 x6))),
  rel_iso (le_iso hx (Nat_add_iso hx0 (Nat_mul_iso hx0 hx1))) x9 x10 ->
  forall (x11 : x3 + x3 * x5 <= x7) (x12 : imported_le (imported_Nat_add x4 (imported_Nat_mul x4 x6)) x8),
  rel_iso (le_iso (Nat_add_iso hx0 (Nat_mul_iso hx0 hx1)) hx2) x11 x12 ->
  rel_iso (le_iso hx hx2) (Original.LF_DOT_AltAuto.LF.AltAuto.trans_example2 x1 x3 x5 x7 x9 x11) (imported_Original_LF__DOT__AltAuto_LF_AltAuto_trans__example2 x10 x12).
Existing Instance Original_LF__DOT__AltAuto_LF_AltAuto_trans__example2_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_AltAuto.LF.AltAuto.trans_example2 ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_trans__example2_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_AltAuto.LF.AltAuto.trans_example2 imported_Original_LF__DOT__AltAuto_LF_AltAuto_trans__example2 ?x) => unify x Original_LF__DOT__AltAuto_LF_AltAuto_trans__example2_iso; constructor : typeclass_instances.


End Interface.