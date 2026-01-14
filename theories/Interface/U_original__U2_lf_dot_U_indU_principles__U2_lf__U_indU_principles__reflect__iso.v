From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__t____tree__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__t____tree__iso.

  Export Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__t____tree__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__t____tree__iso.Args <+ Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__t____tree__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_reflect : forall x : Type, imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree x -> imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree x.
Parameter Original_LF__DOT__IndPrinciples_LF_IndPrinciples_reflect_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.t_tree x1) (x4 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree x2),
  rel_iso (Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree_iso hx) x3 x4 ->
  rel_iso (Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree_iso hx) (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.reflect x3)
    (imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_reflect x4).
Existing Instance Original_LF__DOT__IndPrinciples_LF_IndPrinciples_reflect_iso.
#[export] Hint Extern 0 (IsoStatementProofFor (@Original.LF_DOT_IndPrinciples.LF.IndPrinciples.reflect) ?x) => unify x Original_LF__DOT__IndPrinciples_LF_IndPrinciples_reflect_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween (@Original.LF_DOT_IndPrinciples.LF.IndPrinciples.reflect) imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_reflect ?x) => unify x Original_LF__DOT__IndPrinciples_LF_IndPrinciples_reflect_iso; constructor : typeclass_instances.


End Interface.