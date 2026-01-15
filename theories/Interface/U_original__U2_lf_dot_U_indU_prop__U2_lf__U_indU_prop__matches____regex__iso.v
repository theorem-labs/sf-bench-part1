From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reflect__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__string__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reflect__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__string__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reflect__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__string__iso.CodeBlocks.

#[export] Instance: MustUnfold Original.LF_DOT_IndProp.LF.IndProp.matches_regex := {}.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reflect__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__string__iso.Interface.

Module Type Interface (Import args : Args).

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_matches__regex : (imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii -> imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp imported_Ascii_ascii -> imported_Original_LF__DOT__Basics_LF_Basics_bool) ->
  SProp
  := fun
    x : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii ->
        imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp imported_Ascii_ascii -> imported_Original_LF__DOT__Basics_LF_Basics_bool =>
  forall (a' : imported_Original_LF__DOT__IndProp_LF_IndProp_string) (a'0 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp imported_Ascii_ascii),
  imported_Original_LF__DOT__IndProp_LF_IndProp_reflect (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match a' a'0) (x a' a'0).
Definition Original_LF__DOT__IndProp_LF_IndProp_matches__regex_iso : forall (x1 : Original.LF_DOT_IndProp.LF.IndProp.string -> Original.LF_DOT_IndProp.LF.IndProp.reg_exp Ascii.ascii -> Original.LF_DOT_Basics.LF.Basics.bool)
    (x2 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii ->
          imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp imported_Ascii_ascii -> imported_Original_LF__DOT__Basics_LF_Basics_bool),
  (forall (x3 : Original.LF_DOT_IndProp.LF.IndProp.string) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii),
   rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso Ascii_ascii_iso) x3 x4 ->
   forall (x5 : Original.LF_DOT_IndProp.LF.IndProp.reg_exp Ascii.ascii) (x6 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp imported_Ascii_ascii),
   rel_iso (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso Ascii_ascii_iso) x5 x6 -> rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso (x1 x3 x5) (x2 x4 x6)) ->
  Iso (Original.LF_DOT_IndProp.LF.IndProp.matches_regex x1) (imported_Original_LF__DOT__IndProp_LF_IndProp_matches__regex x2)
  := fun (x1 : Original.LF_DOT_IndProp.LF.IndProp.string -> Original.LF_DOT_IndProp.LF.IndProp.reg_exp Ascii.ascii -> Original.LF_DOT_Basics.LF.Basics.bool)
    (x2 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii ->
          imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp imported_Ascii_ascii -> imported_Original_LF__DOT__Basics_LF_Basics_bool)
    (hx : forall (x3 : Original.LF_DOT_IndProp.LF.IndProp.string) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list imported_Ascii_ascii),
          rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso Ascii_ascii_iso) x3 x4 ->
          forall (x5 : Original.LF_DOT_IndProp.LF.IndProp.reg_exp Ascii.ascii) (x6 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp imported_Ascii_ascii),
          rel_iso (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso Ascii_ascii_iso) x5 x6 -> rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso (x1 x3 x5) (x2 x4 x6)) =>
  IsoForall
    (fun a : Original.LF_DOT_IndProp.LF.IndProp.string =>
     forall re : Original.LF_DOT_IndProp.LF.IndProp.reg_exp Ascii.ascii, Original.LF_DOT_IndProp.LF.IndProp.reflect (Original.LF_DOT_IndProp.LF.IndProp.exp_match a re) (x1 a re))
    (fun x4 : imported_Original_LF__DOT__IndProp_LF_IndProp_string =>
     forall a' : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp imported_Ascii_ascii,
     imported_Original_LF__DOT__IndProp_LF_IndProp_reflect (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match x4 a') (x2 x4 a'))
    (fun (x3 : Original.LF_DOT_IndProp.LF.IndProp.string) (x4 : imported_Original_LF__DOT__IndProp_LF_IndProp_string) (hx0 : rel_iso Original_LF__DOT__IndProp_LF_IndProp_string_iso x3 x4) =>
     IsoForall (fun a : Original.LF_DOT_IndProp.LF.IndProp.reg_exp Ascii.ascii => Original.LF_DOT_IndProp.LF.IndProp.reflect (Original.LF_DOT_IndProp.LF.IndProp.exp_match x3 a) (x1 x3 a))
       (fun x6 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp imported_Ascii_ascii =>
        imported_Original_LF__DOT__IndProp_LF_IndProp_reflect (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match x4 x6) (x2 x4 x6))
       (fun (x5 : Original.LF_DOT_IndProp.LF.IndProp.reg_exp Ascii.ascii) (x6 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp imported_Ascii_ascii)
          (hx1 : rel_iso (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso Ascii_ascii_iso) x5 x6) =>
        relax_Iso_Ts_Ps (Original_LF__DOT__IndProp_LF_IndProp_reflect_iso (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso hx0 hx1) (hx x3 x4 hx0 x5 x6 hx1)))).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_matches__regex_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.matches_regex ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_matches__regex_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.matches_regex imported_Original_LF__DOT__IndProp_LF_IndProp_matches__regex ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_matches__regex_iso; constructor : typeclass_instances.


End Interface.