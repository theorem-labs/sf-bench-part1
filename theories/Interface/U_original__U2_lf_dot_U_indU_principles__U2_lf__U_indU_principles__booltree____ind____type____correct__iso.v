From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__booltree__iso Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__booltree____property____type__iso Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__base____case__iso Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__branch____case__iso Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__leaf____case__iso Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__booltree____ind____type__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__booltree__iso Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__booltree____property____type__iso Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__base____case__iso Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__branch____case__iso Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__leaf____case__iso Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__booltree____ind____type__iso.

  Export Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__booltree__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__booltree____property____type__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__base____case__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__branch____case__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__leaf____case__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__booltree____ind____type__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__booltree__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__booltree____property____type__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__base____case__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__branch____case__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__leaf____case__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__booltree____ind____type__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__ind__type__correct : forall x : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree -> SProp,
  imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_base__case (fun x0 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree => x x0) ->
  imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_leaf__case (fun x0 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree => x x0) ->
  imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_branch__case (fun x0 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree => x x0) ->
  forall x3 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree, x x3.
Parameter Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__ind__type__correct_iso : forall (x1 : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree_property_type) (x2 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree -> SProp)
    (hx : forall (x3 : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree) (x4 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree),
          rel_iso Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree_iso x3 x4 -> Iso (x1 x3) (x2 x4))
    (x3 : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.base_case x1)
    (x4 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_base__case (fun x : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree => x2 x)),
  rel_iso
    (Original_LF__DOT__IndPrinciples_LF_IndPrinciples_base__case_iso x1 (fun x : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree => x2 x)
       (fun (x5 : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree) (x6 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree)
          (hx0 : rel_iso Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree_iso x5 x6) =>
        hx x5 x6 hx0))
    x3 x4 ->
  forall (x5 : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.leaf_case x1)
    (x6 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_leaf__case (fun x : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree => x2 x)),
  rel_iso
    (Original_LF__DOT__IndPrinciples_LF_IndPrinciples_leaf__case_iso x1 (fun x : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree => x2 x)
       (fun (x7 : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree) (x8 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree)
          (hx1 : rel_iso Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree_iso x7 x8) =>
        hx x7 x8 hx1))
    x5 x6 ->
  forall (x7 : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.branch_case x1)
    (x8 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_branch__case (fun x : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree => x2 x)),
  rel_iso
    (Original_LF__DOT__IndPrinciples_LF_IndPrinciples_branch__case_iso x1 (fun x : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree => x2 x)
       (fun (x9 : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree) (x10 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree)
          (hx2 : rel_iso Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree_iso x9 x10) =>
        hx x9 x10 hx2))
    x7 x8 ->
  forall (x9 : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree) (x10 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree)
    (hx3 : rel_iso Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree_iso x9 x10),
  rel_iso (hx x9 x10 hx3) (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree_ind_type_correct x1 x3 x5 x7 x9)
    (imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__ind__type__correct x2 x4 x6 x8 x10).
Existing Instance Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__ind__type__correct_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree_ind_type_correct ?x) => unify x Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__ind__type__correct_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree_ind_type_correct imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__ind__type__correct ?x) => unify x Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__ind__type__correct_iso; constructor : typeclass_instances.


End Interface.