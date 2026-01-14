From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_match__eps : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp imported_Ascii_ascii -> imported_Original_LF__DOT__Basics_LF_Basics_bool.
Parameter Original_LF__DOT__IndProp_LF_IndProp_match__eps_iso : forall (x1 : Original.LF_DOT_IndProp.LF.IndProp.reg_exp Ascii.ascii) (x2 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp imported_Ascii_ascii),
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso Ascii_ascii_iso) x1 x2 ->
  rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso (Original.LF_DOT_IndProp.LF.IndProp.match_eps x1) (imported_Original_LF__DOT__IndProp_LF_IndProp_match__eps x2).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_match__eps_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.match_eps ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_match__eps_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.match_eps imported_Original_LF__DOT__IndProp_LF_IndProp_match__eps ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_match__eps_iso; constructor : typeclass_instances.


End Interface.