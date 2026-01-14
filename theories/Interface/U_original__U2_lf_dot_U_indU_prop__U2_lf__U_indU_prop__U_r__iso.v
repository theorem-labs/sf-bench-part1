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

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_R : imported_nat -> imported_nat -> imported_nat -> SProp.
Parameter Original_LF__DOT__IndProp_LF_IndProp_R_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 ->
  forall (x3 : nat) (x4 : imported_nat),
  rel_iso nat_iso x3 x4 ->
  forall (x5 : nat) (x6 : imported_nat), rel_iso nat_iso x5 x6 -> Iso (Original.LF_DOT_IndProp.LF.IndProp.R x1 x3 x5) (imported_Original_LF__DOT__IndProp_LF_IndProp_R x2 x4 x6).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_R_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.R ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_R_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.R imported_Original_LF__DOT__IndProp_LF_IndProp_R ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_R_iso; constructor : typeclass_instances.


End Interface.