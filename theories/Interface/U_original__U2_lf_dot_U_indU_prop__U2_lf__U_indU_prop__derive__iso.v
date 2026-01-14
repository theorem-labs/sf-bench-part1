From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_derive : imported_Ascii_ascii -> imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp imported_Ascii_ascii -> imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp imported_Ascii_ascii.
Parameter Original_LF__DOT__IndProp_LF_IndProp_derive_iso : forall (x1 : Ascii.ascii) (x2 : imported_Ascii_ascii),
  rel_iso Ascii_ascii_iso x1 x2 ->
  forall (x3 : Original.LF_DOT_IndProp.LF.IndProp.reg_exp Ascii.ascii) (x4 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp imported_Ascii_ascii),
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso Ascii_ascii_iso) x3 x4 ->
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso Ascii_ascii_iso) (Original.LF_DOT_IndProp.LF.IndProp.derive x1 x3) (imported_Original_LF__DOT__IndProp_LF_IndProp_derive x2 x4).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_derive_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.derive ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_derive_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.derive imported_Original_LF__DOT__IndProp_LF_IndProp_derive ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_derive_iso; constructor : typeclass_instances.


End Interface.