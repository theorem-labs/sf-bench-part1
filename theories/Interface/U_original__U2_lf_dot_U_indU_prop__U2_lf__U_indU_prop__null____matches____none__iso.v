From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.U_original__U_false__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_emptyU_set__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__string__iso Interface.iff__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.U_original__U_false__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_emptyU_set__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__string__iso Interface.iff__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.U_original__U_false__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_emptyU_set__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__string__iso.CodeBlocks Interface.iff__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.U_original__U_false__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_emptyU_set__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__string__iso.Interface <+ Interface.iff__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_null__matches__none : forall x : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii,
  imported_iff (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match x (imported_Original_LF__DOT__IndProp_LF_IndProp_EmptySet imported_Ascii_ascii)) imported_Original_False.
Parameter Original_LF__DOT__IndProp_LF_IndProp_null__matches__none_iso : forall (x1 : Original.LF_DOT_IndProp.LF.IndProp.string) (x2 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii)
    (hx : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso Ascii_ascii_iso) x1 x2),
  rel_iso
    {|
      to := iff_iso (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso hx (Original_LF__DOT__IndProp_LF_IndProp_EmptySet_iso Ascii_ascii_iso)) Original_False_iso;
      from := from (iff_iso (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso hx (Original_LF__DOT__IndProp_LF_IndProp_EmptySet_iso Ascii_ascii_iso)) Original_False_iso);
      to_from :=
        fun x : imported_iff (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match x2 (imported_Original_LF__DOT__IndProp_LF_IndProp_EmptySet imported_Ascii_ascii)) imported_Original_False =>
        to_from (iff_iso (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso hx (Original_LF__DOT__IndProp_LF_IndProp_EmptySet_iso Ascii_ascii_iso)) Original_False_iso) x;
      from_to :=
        fun x : Original.LF_DOT_IndProp.LF.IndProp.exp_match x1 Original.LF_DOT_IndProp.LF.IndProp.EmptySet <-> Original.False =>
        seq_p_of_t (from_to (iff_iso (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso hx (Original_LF__DOT__IndProp_LF_IndProp_EmptySet_iso Ascii_ascii_iso)) Original_False_iso) x)
    |} (Original.LF_DOT_IndProp.LF.IndProp.null_matches_none x1) (imported_Original_LF__DOT__IndProp_LF_IndProp_null__matches__none x2).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_null__matches__none_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.null_matches_none ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_null__matches__none_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.null_matches_none imported_Original_LF__DOT__IndProp_LF_IndProp_null__matches__none ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_null__matches__none_iso; constructor : typeclass_instances.


End Interface.