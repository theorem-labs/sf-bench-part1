From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__booltree__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__booltree__iso.

  Export Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__booltree__iso.CodeBlocks.

#[export] Instance: MustUnfold Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree_property_type := {}.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__booltree__iso.Args <+ Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__booltree__iso.Interface.

Module Type Interface (Import args : Args).

Definition imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__property__type : Type
  := imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree -> SProp.
Definition Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__property__type_iso : Iso Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree_property_type imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__property__type
  := IsoArrow Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree_iso iso_Prop_SProp.
Existing Instance Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__property__type_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree_property_type ?x) => unify x Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__property__type_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree_property_type imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__property__type ?x) => unify x Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__property__type_iso; constructor : typeclass_instances.


End Interface.