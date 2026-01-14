From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.nat__iso Interface.__0__iso Interface.le__iso.

Module Export CodeBlocks.

  Export (hints) Interface.nat__iso Interface.__0__iso Interface.le__iso.

  Export Interface.nat__iso.CodeBlocks Interface.__0__iso.CodeBlocks Interface.le__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.nat__iso.Interface <+ Interface.__0__iso.Interface <+ Interface.le__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_O__le__n : forall x : imported_nat, imported_le imported_0 x.
Parameter Original_LF__DOT__IndProp_LF_IndProp_O__le__n_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2),
  rel_iso (le_iso _0_iso hx) (Original.LF_DOT_IndProp.LF.IndProp.O_le_n x1) (imported_Original_LF__DOT__IndProp_LF_IndProp_O__le__n x2).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_O__le__n_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.O_le_n ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_O__le__n_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.O_le_n imported_Original_LF__DOT__IndProp_LF_IndProp_O__le__n ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_O__le__n_iso; constructor : typeclass_instances.


End Interface.