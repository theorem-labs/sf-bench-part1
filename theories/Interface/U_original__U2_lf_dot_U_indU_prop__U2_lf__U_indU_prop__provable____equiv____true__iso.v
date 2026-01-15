From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_true__iso Interface.iff__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_true__iso Interface.iff__iso.

  Export Interface.U_true__iso.CodeBlocks Interface.iff__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_true__iso.Interface <+ Interface.iff__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_provable__equiv__true : forall x : SProp, x -> imported_iff x imported_True.
Parameter Original_LF__DOT__IndProp_LF_IndProp_provable__equiv__true_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2),
  rel_iso hx x3 x4 ->
  rel_iso (relax_Iso_Ts_Ps (iff_iso hx True_iso)) (Original.LF_DOT_IndProp.LF.IndProp.provable_equiv_true x1 x3) (imported_Original_LF__DOT__IndProp_LF_IndProp_provable__equiv__true x4).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_provable__equiv__true_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.provable_equiv_true ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_provable__equiv__true_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.provable_equiv_true imported_Original_LF__DOT__IndProp_LF_IndProp_provable__equiv__true ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_provable__equiv__true_iso; constructor : typeclass_instances.


End Interface.