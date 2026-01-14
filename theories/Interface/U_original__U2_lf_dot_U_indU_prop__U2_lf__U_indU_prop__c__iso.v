From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Args <+ Interface.U_ascii__ascii__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_c : imported_Ascii_ascii.
Parameter Original_LF__DOT__IndProp_LF_IndProp_c_iso : rel_iso Ascii_ascii_iso Original.LF_DOT_IndProp.LF.IndProp.c imported_Original_LF__DOT__IndProp_LF_IndProp_c.
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_c_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.c ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_c_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.c imported_Original_LF__DOT__IndProp_LF_IndProp_c ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_c_iso; constructor : typeclass_instances.


End Interface.