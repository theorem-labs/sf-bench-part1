From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_induction__U2_lf__U_induction__bin__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_induction__U2_lf__U_induction__bin__iso.

  Export Interface.U_original__U2_lf_dot_U_induction__U2_lf__U_induction__bin__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_induction__U2_lf__U_induction__bin__iso.Args <+ Interface.U_original__U2_lf_dot_U_induction__U2_lf__U_induction__bin__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Induction_LF_Induction_Z : imported_Original_LF__DOT__Induction_LF_Induction_bin.
Parameter Original_LF__DOT__Induction_LF_Induction_Z_iso : rel_iso Original_LF__DOT__Induction_LF_Induction_bin_iso Original.LF_DOT_Induction.LF.Induction.Z imported_Original_LF__DOT__Induction_LF_Induction_Z.
Existing Instance Original_LF__DOT__Induction_LF_Induction_Z_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Induction.LF.Induction.Z ?x) => unify x Original_LF__DOT__Induction_LF_Induction_Z_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Induction.LF.Induction.Z imported_Original_LF__DOT__Induction_LF_Induction_Z ?x) => unify x Original_LF__DOT__Induction_LF_Induction_Z_iso; constructor : typeclass_instances.


End Interface.