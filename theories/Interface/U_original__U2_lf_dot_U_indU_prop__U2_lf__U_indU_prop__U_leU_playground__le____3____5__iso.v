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

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le__3__5 : imported_le (imported_S (imported_S (imported_S imported_0))) (imported_S (imported_S (imported_S (iterate1 imported_S 2 imported_0)))).
Parameter Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le__3__5_iso : rel_iso (le_iso (S_iso (S_iso (S_iso _0_iso))) (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 2 0 imported_0 _0_iso))))) Original.LF_DOT_IndProp.LF.IndProp.LePlayground.le_3_5
    imported_Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le__3__5.
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le__3__5_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.LePlayground.le_3_5 ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le__3__5_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.LePlayground.le_3_5 imported_Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le__3__5 ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le__3__5_iso; constructor : typeclass_instances.


End Interface.