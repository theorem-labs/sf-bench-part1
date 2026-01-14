From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.nat__iso.

Module Export CodeBlocks.

  Export (hints) Interface.nat__iso.

  Export Interface.nat__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.nat__iso.Args <+ Interface.nat__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_le : imported_nat -> imported_nat -> SProp.
Parameter Original_LF__DOT__IndProp_LF_IndProp_le_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 -> forall (x3 : nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> Iso (Original.LF_DOT_IndProp.LF.IndProp.le x1 x3) (imported_Original_LF__DOT__IndProp_LF_IndProp_le x2 x4).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_le_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.le ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_le_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.le imported_Original_LF__DOT__IndProp_LF_IndProp_le ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_le_iso; constructor : typeclass_instances.


End Interface.