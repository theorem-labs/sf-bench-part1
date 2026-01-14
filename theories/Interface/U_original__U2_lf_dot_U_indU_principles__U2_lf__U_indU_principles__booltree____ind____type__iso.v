From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__booltree__iso Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__booltree____property____type__iso Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__base____case__iso Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__branch____case__iso Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__leaf____case__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__booltree__iso Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__booltree____property____type__iso Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__base____case__iso Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__branch____case__iso Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__leaf____case__iso.

  Export Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__booltree__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__booltree____property____type__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__base____case__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__branch____case__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__leaf____case__iso.CodeBlocks.

#[export] Instance: MustUnfold Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree_ind_type := {}.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__booltree__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__booltree____property____type__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__base____case__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__branch____case__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__leaf____case__iso.Interface.

Module Type Interface (Import args : Args).

Definition imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__ind__type : SProp
  := forall x2 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree -> SProp,
  imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_base__case (fun H : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree => x2 H) ->
  imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_leaf__case (fun H : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree => x2 H) ->
  imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_branch__case (fun H : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree => x2 H) ->
  forall a' : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree, x2 a'.
Definition Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__ind__type_iso : forall (x1 : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree_property_type) (x2 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree -> SProp),
  (forall (x3 : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree) (x4 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree),
   rel_iso Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree_iso x3 x4 -> Iso (x1 x3) (x2 x4)) ->
  Iso
    (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.base_case x1 ->
     Original.LF_DOT_IndPrinciples.LF.IndPrinciples.leaf_case x1 ->
     Original.LF_DOT_IndPrinciples.LF.IndPrinciples.branch_case x1 -> forall b : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree, x1 b)
    (imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_base__case (fun H : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree => x2 H) ->
     imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_leaf__case (fun H : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree => x2 H) ->
     imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_branch__case (fun H : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree => x2 H) ->
     forall a' : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree, x2 a')
  := fun (x1 : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree_property_type) (x2 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree -> SProp)
    (hx : forall (x3 : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree) (x4 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree),
          rel_iso Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree_iso x3 x4 -> Iso (x1 x3) (x2 x4)) =>
  IsoArrow
    (Original_LF__DOT__IndPrinciples_LF_IndPrinciples_base__case_iso x1 (fun H : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree => x2 H)
       (fun (x3 : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree) (x4 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree)
          (hx0 : rel_iso Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree_iso x3 x4) =>
        hx x3 x4 hx0))
    (IsoArrow
       (Original_LF__DOT__IndPrinciples_LF_IndPrinciples_leaf__case_iso x1 (fun H : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree => x2 H)
          (fun (x3 : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree) (x4 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree)
             (hx0 : rel_iso Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree_iso x3 x4) =>
           hx x3 x4 hx0))
       (IsoArrow
          (Original_LF__DOT__IndPrinciples_LF_IndPrinciples_branch__case_iso x1 (fun H : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree => x2 H)
             (fun (x3 : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree) (x4 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree)
                (hx0 : rel_iso Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree_iso x3 x4) =>
              hx x3 x4 hx0))
          (IsoForall x1 (fun x4 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree => x2 x4)
             (fun (x3 : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree) (x4 : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree)
                (hx0 : rel_iso Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree_iso x3 x4) =>
              hx x3 x4 hx0)))).
Existing Instance Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__ind__type_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree_ind_type ?x) => unify x Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__ind__type_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndPrinciples.LF.IndPrinciples.booltree_ind_type imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__ind__type ?x) => unify x Original_LF__DOT__IndPrinciples_LF_IndPrinciples_booltree__ind__type_iso; constructor : typeclass_instances.


End Interface.