From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__booltree__iso Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__booltree____property____type__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__booltree__iso Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__booltree____property____type__iso.

  Export Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__booltree__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__booltree____property____type__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__booltree__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__booltree____property____type__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_branch__case : (imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree -> SProp) -> SProp.
Parameter Original_LF__DOT__IndPrinciples_LF_IndPrinciples_branch__case_iso : forall (x1 : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree_property_type) (x2 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree -> SProp),
  (forall (x3 : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree) (x4 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree),
   rel_iso Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree_iso x3 x4 -> Iso (x1 x3) (x2 x4)) ->
  Iso (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.branch_case x1) (imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_branch__case x2).
Existing Instance Original_LF__DOT__IndPrinciples_LF_IndPrinciples_branch__case_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndPrinciples.LF.IndPrinciples.branch_case ?x) => unify x Original_LF__DOT__IndPrinciples_LF_IndPrinciples_branch__case_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndPrinciples.LF.IndPrinciples.branch_case imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_branch__case ?x) => unify x Original_LF__DOT__IndPrinciples_LF_IndPrinciples_branch__case_iso; constructor : typeclass_instances.


End Interface.