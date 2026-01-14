From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_person__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_person__iso.

  Export Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_person__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_person__iso.Args <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_person__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_parent__of : imported_Original_LF__DOT__IndProp_LF_IndProp_Person -> imported_Original_LF__DOT__IndProp_LF_IndProp_Person -> SProp.
Parameter Original_LF__DOT__IndProp_LF_IndProp_parent__of_iso : forall (x1 : Original.LF_DOT_IndProp.LF.IndProp.Person) (x2 : imported_Original_LF__DOT__IndProp_LF_IndProp_Person),
  rel_iso Original_LF__DOT__IndProp_LF_IndProp_Person_iso x1 x2 ->
  forall (x3 : Original.LF_DOT_IndProp.LF.IndProp.Person) (x4 : imported_Original_LF__DOT__IndProp_LF_IndProp_Person),
  rel_iso Original_LF__DOT__IndProp_LF_IndProp_Person_iso x3 x4 -> Iso (Original.LF_DOT_IndProp.LF.IndProp.parent_of x1 x3) (imported_Original_LF__DOT__IndProp_LF_IndProp_parent__of x2 x4).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_parent__of_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.parent_of ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_parent__of_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.parent_of imported_Original_LF__DOT__IndProp_LF_IndProp_parent__of ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_parent__of_iso; constructor : typeclass_instances.


End Interface.