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

Parameter imported_Original_LF__DOT__Induction_LF_Induction_double__bin : imported_Original_LF__DOT__Induction_LF_Induction_bin -> imported_Original_LF__DOT__Induction_LF_Induction_bin.
Parameter Original_LF__DOT__Induction_LF_Induction_double__bin_iso : forall (x1 : Original.LF_DOT_Induction.LF.Induction.bin) (x2 : imported_Original_LF__DOT__Induction_LF_Induction_bin),
  rel_iso Original_LF__DOT__Induction_LF_Induction_bin_iso x1 x2 ->
  rel_iso Original_LF__DOT__Induction_LF_Induction_bin_iso (Original.LF_DOT_Induction.LF.Induction.double_bin x1) (imported_Original_LF__DOT__Induction_LF_Induction_double__bin x2).
Existing Instance Original_LF__DOT__Induction_LF_Induction_double__bin_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Induction.LF.Induction.double_bin ?x) => unify x Original_LF__DOT__Induction_LF_Induction_double__bin_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Induction.LF.Induction.double_bin imported_Original_LF__DOT__Induction_LF_Induction_double__bin ?x) => unify x Original_LF__DOT__Induction_LF_Induction_double__bin_iso; constructor : typeclass_instances.


End Interface.