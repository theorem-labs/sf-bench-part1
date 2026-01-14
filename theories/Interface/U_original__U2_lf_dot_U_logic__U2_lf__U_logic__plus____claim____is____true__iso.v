From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__plus____claim__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__plus____claim__iso.

  Export Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__plus____claim__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__plus____claim__iso.Args <+ Interface.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__plus____claim__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_plus__claim__is__true : imported_Original_LF__DOT__Logic_LF_Logic_plus__claim.
Parameter Original_LF__DOT__Logic_LF_Logic_plus__claim__is__true_iso : rel_iso Original_LF__DOT__Logic_LF_Logic_plus__claim_iso Original.LF_DOT_Logic.LF.Logic.plus_claim_is_true imported_Original_LF__DOT__Logic_LF_Logic_plus__claim__is__true.
Existing Instance Original_LF__DOT__Logic_LF_Logic_plus__claim__is__true_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.plus_claim_is_true ?x) => unify x Original_LF__DOT__Logic_LF_Logic_plus__claim__is__true_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.plus_claim_is_true imported_Original_LF__DOT__Logic_LF_Logic_plus__claim__is__true ?x) => unify x Original_LF__DOT__Logic_LF_Logic_plus__claim__is__true_iso; constructor : typeclass_instances.


End Interface.