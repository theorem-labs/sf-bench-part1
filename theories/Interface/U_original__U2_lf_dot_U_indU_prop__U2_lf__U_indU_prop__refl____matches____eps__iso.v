From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reflect__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reflect__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reflect__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.CodeBlocks.

#[export] Instance: MustUnfold Original.LF_DOT_IndProp.LF.IndProp.refl_matches_eps := {}.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reflect__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__exp____match__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.Interface.

Module Type Interface (Import args : Args).

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_refl__matches__eps : (imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp imported_Ascii_ascii -> imported_Original_LF__DOT__Basics_LF_Basics_bool) -> SProp
  := fun x : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp imported_Ascii_ascii -> imported_Original_LF__DOT__Basics_LF_Basics_bool =>
  forall a' : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp imported_Ascii_ascii,
  imported_Original_LF__DOT__IndProp_LF_IndProp_reflect (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_Ascii_ascii) a') (x a').
Definition Original_LF__DOT__IndProp_LF_IndProp_refl__matches__eps_iso : forall (x1 : Original.LF_DOT_IndProp.LF.IndProp.reg_exp Ascii.ascii -> Original.LF_DOT_Basics.LF.Basics.bool)
    (x2 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp imported_Ascii_ascii -> imported_Original_LF__DOT__Basics_LF_Basics_bool),
  (forall (x3 : Original.LF_DOT_IndProp.LF.IndProp.reg_exp Ascii.ascii) (x4 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp imported_Ascii_ascii),
   rel_iso (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso Ascii_ascii_iso) x3 x4 -> rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso (x1 x3) (x2 x4)) ->
  Iso (Original.LF_DOT_IndProp.LF.IndProp.refl_matches_eps x1) (imported_Original_LF__DOT__IndProp_LF_IndProp_refl__matches__eps x2)
  := fun (x1 : Original.LF_DOT_IndProp.LF.IndProp.reg_exp Ascii.ascii -> Original.LF_DOT_Basics.LF.Basics.bool)
    (x2 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp imported_Ascii_ascii -> imported_Original_LF__DOT__Basics_LF_Basics_bool)
    (hx : forall (x3 : Original.LF_DOT_IndProp.LF.IndProp.reg_exp Ascii.ascii) (x4 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp imported_Ascii_ascii),
          rel_iso (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso Ascii_ascii_iso) x3 x4 -> rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso (x1 x3) (x2 x4)) =>
  IsoForall
    (fun a : Original.LF_DOT_IndProp.LF.IndProp.reg_exp Ascii.ascii =>
     Original.LF_DOT_IndProp.LF.IndProp.reflect (Original.LF_DOT_IndProp.LF.IndProp.exp_match Original.LF_DOT_Poly.LF.Poly.nil a) (x1 a))
    (fun x4 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp imported_Ascii_ascii =>
     imported_Original_LF__DOT__IndProp_LF_IndProp_reflect (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_Ascii_ascii) x4) (x2 x4))
    (fun (x3 : Original.LF_DOT_IndProp.LF.IndProp.reg_exp Ascii.ascii) (x4 : imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp imported_Ascii_ascii)
       (hx0 : rel_iso (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso Ascii_ascii_iso) x3 x4) =>
     {|
       to := Original_LF__DOT__IndProp_LF_IndProp_reflect_iso (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso (Original_LF__DOT__Poly_LF_Poly_nil_iso Ascii_ascii_iso) hx0) (hx x3 x4 hx0);
       from :=
         from (Original_LF__DOT__IndProp_LF_IndProp_reflect_iso (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso (Original_LF__DOT__Poly_LF_Poly_nil_iso Ascii_ascii_iso) hx0) (hx x3 x4 hx0));
       to_from :=
         fun
           x : imported_Original_LF__DOT__IndProp_LF_IndProp_reflect (imported_Original_LF__DOT__IndProp_LF_IndProp_exp__match (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_Ascii_ascii) x4)
                 (x2 x4) =>
         to_from (Original_LF__DOT__IndProp_LF_IndProp_reflect_iso (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso (Original_LF__DOT__Poly_LF_Poly_nil_iso Ascii_ascii_iso) hx0) (hx x3 x4 hx0)) x;
       from_to :=
         fun x : Original.LF_DOT_IndProp.LF.IndProp.reflect (Original.LF_DOT_IndProp.LF.IndProp.exp_match Original.LF_DOT_Poly.LF.Poly.nil x3) (x1 x3) =>
         seq_p_of_t
           (from_to
              (Original_LF__DOT__IndProp_LF_IndProp_reflect_iso (Original_LF__DOT__IndProp_LF_IndProp_exp__match_iso (Original_LF__DOT__Poly_LF_Poly_nil_iso Ascii_ascii_iso) hx0) (hx x3 x4 hx0)) x)
     |}).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_refl__matches__eps_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.refl_matches_eps ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_refl__matches__eps_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.refl_matches_eps imported_Original_LF__DOT__IndProp_LF_IndProp_refl__matches__eps ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_refl__matches__eps_iso; constructor : typeclass_instances.


End Interface.