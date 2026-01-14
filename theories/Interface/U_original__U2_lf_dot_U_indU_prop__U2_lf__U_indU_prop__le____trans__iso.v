From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.nat__iso Interface.le__iso.

Module Export CodeBlocks.

  Export (hints) Interface.nat__iso Interface.le__iso.

  Export Interface.nat__iso.CodeBlocks Interface.le__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.nat__iso.Interface <+ Interface.le__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_le__trans : forall x x0 x1 : imported_nat, imported_le x x0 -> imported_le x0 x1 -> imported_le x x1.
Parameter Original_LF__DOT__IndProp_LF_IndProp_le__trans_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) (x5 : nat) (x6 : imported_nat) (hx1 : rel_iso nat_iso x5 x6)
    (x7 : x1 <= x3) (x8 : imported_le x2 x4),
  rel_iso (le_iso hx hx0) x7 x8 ->
  forall (x9 : x3 <= x5) (x10 : imported_le x4 x6),
  rel_iso (le_iso hx0 hx1) x9 x10 -> rel_iso (le_iso hx hx1) (Original.LF_DOT_IndProp.LF.IndProp.le_trans x1 x3 x5 x7 x9) (imported_Original_LF__DOT__IndProp_LF_IndProp_le__trans x8 x10).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_le__trans_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.le_trans ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_le__trans_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.le_trans imported_Original_LF__DOT__IndProp_LF_IndProp_le__trans ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_le__trans_iso; constructor : typeclass_instances.


End Interface.