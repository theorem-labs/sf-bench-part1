From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.nat__iso Interface.U_s__iso Interface.__0__iso Interface.le__iso.

Module Export CodeBlocks.

  Export (hints) Interface.nat__iso Interface.U_s__iso Interface.__0__iso Interface.le__iso.

  Export Interface.nat__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks Interface.le__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.nat__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface <+ Interface.le__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_test__le1 : imported_le (imported_S (imported_S (imported_S imported_0))) (imported_S (imported_S (imported_S imported_0))).
Parameter Original_LF__DOT__IndProp_LF_IndProp_test__le1_iso : rel_iso (le_iso (S_iso (S_iso (S_iso _0_iso))) (S_iso (S_iso (S_iso _0_iso)))) Original.LF_DOT_IndProp.LF.IndProp.test_le1 imported_Original_LF__DOT__IndProp_LF_IndProp_test__le1.
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_test__le1_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.test_le1 ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_test__le1_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.test_le1 imported_Original_LF__DOT__IndProp_LF_IndProp_test__le1 ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_test__le1_iso; constructor : typeclass_instances.


End Interface.