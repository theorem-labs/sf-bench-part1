From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__U_repeat__com__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aminus__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aplus__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__bexp__iso Interface.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__U_repeat__U2_cif__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_ble__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__U_repeat__U2_casgn__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aid__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_x__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_y__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_z__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.ex__iso Interface.false__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__empty____st__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso Interface.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__U_repeat__ceval__iso Interface.U_s__iso Interface.__0__iso Interface.true__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__U_repeat__com__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aminus__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aplus__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__bexp__iso Interface.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__U_repeat__U2_cif__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_ble__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__U_repeat__U2_casgn__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aid__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_x__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_y__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_z__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.ex__iso Interface.false__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__empty____st__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso Interface.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__U_repeat__ceval__iso Interface.U_s__iso Interface.__0__iso Interface.true__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__U_repeat__com__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aminus__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aplus__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__bexp__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__U_repeat__U2_cif__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_ble__iso.CodeBlocks Interface.U_string__string__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__U_repeat__U2_casgn__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aid__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_x__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_y__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_z__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update__iso.CodeBlocks Interface.U_string__U_emptyU_string__iso.CodeBlocks Interface.U_string__U_string__iso.CodeBlocks Interface.bool__iso.CodeBlocks Interface.U_ascii__U_ascii__iso.CodeBlocks Interface.ex__iso.CodeBlocks Interface.false__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__empty____st__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__U_repeat__ceval__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks Interface.true__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__U_repeat__com__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aminus__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aplus__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__bexp__iso.Interface <+ Interface.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__U_repeat__U2_cif__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_ble__iso.Interface <+ Interface.U_string__string__iso.Interface <+ Interface.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__U_repeat__U2_casgn__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aid__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_x__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_y__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_z__iso.Interface <+ Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.Interface <+ Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update__iso.Interface <+ Interface.U_string__U_emptyU_string__iso.Interface <+ Interface.U_string__U_string__iso.Interface <+ Interface.bool__iso.Interface <+ Interface.U_ascii__U_ascii__iso.Interface <+ Interface.ex__iso.Interface <+ Interface.false__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__empty____st__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.Interface <+ Interface.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__U_repeat__ceval__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface <+ Interface.true__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Auto_LF_Auto_eauto__example : imported_ex
    (fun H : imported_String_string -> imported_nat =>
     imported_Original_LF__DOT__Auto_LF_Auto_Repeat_ceval
       (imported_Original_LF__DOT__Auto_LF_Auto_Repeat_CIf
          (imported_Original_LF__DOT__Imp_LF_Imp_BLe (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_X)
             (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_Y))
          (imported_Original_LF__DOT__Auto_LF_Auto_Repeat_CAsgn imported_Original_LF__DOT__Imp_LF_Imp_Z
             (imported_Original_LF__DOT__Imp_LF_Imp_AMinus (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_Y)
                (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_X)))
          (imported_Original_LF__DOT__Auto_LF_Auto_Repeat_CAsgn imported_Original_LF__DOT__Imp_LF_Imp_Y
             (imported_Original_LF__DOT__Imp_LF_Imp_APlus (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_X)
                (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_Z))))
       (fun H0 : imported_String_string =>
        imported_Original_LF__DOT__Maps_LF_Maps_t__update
          (fun H1 : imported_String_string =>
           imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun H2 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st H2) imported_Original_LF__DOT__Imp_LF_Imp_X
             (imported_S (imported_S imported_0)) H1)
          imported_Original_LF__DOT__Imp_LF_Imp_Y (imported_S imported_0) H0)
       (fun H0 : imported_String_string => H H0)).
Parameter Original_LF__DOT__Auto_LF_Auto_eauto__example_iso : rel_iso
    {|
      to :=
        ex_iso
          (fun s' : Original.LF_DOT_Imp.LF.Imp.state =>
           Original.LF_DOT_Auto.LF.Auto.Repeat.ceval
             (Original.LF_DOT_Auto.LF.Auto.Repeat.CIf
                (Original.LF_DOT_Imp.LF.Imp.BLe (Original.LF_DOT_Imp.LF.Imp.AId Original.LF_DOT_Imp.LF.Imp.X) (Original.LF_DOT_Imp.LF.Imp.AId Original.LF_DOT_Imp.LF.Imp.Y))
                (Original.LF_DOT_Auto.LF.Auto.Repeat.CAsgn Original.LF_DOT_Imp.LF.Imp.Z
                   (Original.LF_DOT_Imp.LF.Imp.AMinus (Original.LF_DOT_Imp.LF.Imp.AId Original.LF_DOT_Imp.LF.Imp.Y) (Original.LF_DOT_Imp.LF.Imp.AId Original.LF_DOT_Imp.LF.Imp.X)))
                (Original.LF_DOT_Auto.LF.Auto.Repeat.CAsgn Original.LF_DOT_Imp.LF.Imp.Y
                   (Original.LF_DOT_Imp.LF.Imp.APlus (Original.LF_DOT_Imp.LF.Imp.AId Original.LF_DOT_Imp.LF.Imp.X) (Original.LF_DOT_Imp.LF.Imp.AId Original.LF_DOT_Imp.LF.Imp.Z))))
             (Original.LF_DOT_Maps.LF.Maps.t_update (Original.LF_DOT_Maps.LF.Maps.t_update Original.LF_DOT_Imp.LF.Imp.empty_st Original.LF_DOT_Imp.LF.Imp.X 2) Original.LF_DOT_Imp.LF.Imp.Y 1) s')
          (fun H : imported_String_string -> imported_nat =>
           imported_Original_LF__DOT__Auto_LF_Auto_Repeat_ceval
             (imported_Original_LF__DOT__Auto_LF_Auto_Repeat_CIf
                (imported_Original_LF__DOT__Imp_LF_Imp_BLe (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_X)
                   (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_Y))
                (imported_Original_LF__DOT__Auto_LF_Auto_Repeat_CAsgn imported_Original_LF__DOT__Imp_LF_Imp_Z
                   (imported_Original_LF__DOT__Imp_LF_Imp_AMinus (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_Y)
                      (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_X)))
                (imported_Original_LF__DOT__Auto_LF_Auto_Repeat_CAsgn imported_Original_LF__DOT__Imp_LF_Imp_Y
                   (imported_Original_LF__DOT__Imp_LF_Imp_APlus (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_X)
                      (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_Z))))
             (fun H0 : imported_String_string =>
              imported_Original_LF__DOT__Maps_LF_Maps_t__update
                (fun H1 : imported_String_string =>
                 imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun H2 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st H2) imported_Original_LF__DOT__Imp_LF_Imp_X
                   (imported_S (imported_S imported_0)) H1)
                imported_Original_LF__DOT__Imp_LF_Imp_Y (imported_S imported_0) H0)
             (fun H0 : imported_String_string => H H0))
          (fun (x1 : Original.LF_DOT_Imp.LF.Imp.state) (x2 : imported_String_string -> imported_nat) (hx : rel_iso (IsoArrow String_string_iso nat_iso) x1 x2) =>
           Original_LF__DOT__Auto_LF_Auto_Repeat_ceval_iso
             (Original_LF__DOT__Auto_LF_Auto_Repeat_CIf_iso
                (Original_LF__DOT__Imp_LF_Imp_BLe_iso (Original_LF__DOT__Imp_LF_Imp_AId_iso Original_LF__DOT__Imp_LF_Imp_X_iso)
                   (Original_LF__DOT__Imp_LF_Imp_AId_iso Original_LF__DOT__Imp_LF_Imp_Y_iso))
                (Original_LF__DOT__Auto_LF_Auto_Repeat_CAsgn_iso Original_LF__DOT__Imp_LF_Imp_Z_iso
                   (Original_LF__DOT__Imp_LF_Imp_AMinus_iso (Original_LF__DOT__Imp_LF_Imp_AId_iso Original_LF__DOT__Imp_LF_Imp_Y_iso)
                      (Original_LF__DOT__Imp_LF_Imp_AId_iso Original_LF__DOT__Imp_LF_Imp_X_iso)))
                (Original_LF__DOT__Auto_LF_Auto_Repeat_CAsgn_iso Original_LF__DOT__Imp_LF_Imp_Y_iso
                   (Original_LF__DOT__Imp_LF_Imp_APlus_iso (Original_LF__DOT__Imp_LF_Imp_AId_iso Original_LF__DOT__Imp_LF_Imp_X_iso)
                      (Original_LF__DOT__Imp_LF_Imp_AId_iso Original_LF__DOT__Imp_LF_Imp_Z_iso))))
             (Original.LF_DOT_Maps.LF.Maps.t_update (Original.LF_DOT_Maps.LF.Maps.t_update Original.LF_DOT_Imp.LF.Imp.empty_st Original.LF_DOT_Imp.LF.Imp.X 2) Original.LF_DOT_Imp.LF.Imp.Y 1)
             (fun H : imported_String_string =>
              imported_Original_LF__DOT__Maps_LF_Maps_t__update
                (fun H0 : imported_String_string =>
                 imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun H1 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st H1) imported_Original_LF__DOT__Imp_LF_Imp_X
                   (imported_S (imported_S imported_0)) H0)
                imported_Original_LF__DOT__Imp_LF_Imp_Y (imported_S imported_0) H)
             (fun (x3 : String.string) (x4 : imported_String_string) (hx0 : rel_iso String_string_iso x3 x4) =>
              unwrap_sprop
                (Original_LF__DOT__Maps_LF_Maps_t__update_iso nat_iso (Original.LF_DOT_Maps.LF.Maps.t_update Original.LF_DOT_Imp.LF.Imp.empty_st Original.LF_DOT_Imp.LF.Imp.X 2)
                   (fun H : imported_String_string =>
                    imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun H0 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st H0) imported_Original_LF__DOT__Imp_LF_Imp_X
                      (imported_S (imported_S imported_0)) H)
                   (fun (x5 : String.string) (x6 : imported_String_string) (hx1 : rel_iso String_string_iso x5 x6) =>
                    {|
                      unwrap_sprop :=
                        unwrap_sprop
                          (Original_LF__DOT__Maps_LF_Maps_t__update_iso nat_iso Original.LF_DOT_Imp.LF.Imp.empty_st
                             (fun H : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st H)
                             (fun (x7 : String.string) (x8 : imported_String_string) (hx2 : rel_iso String_string_iso x7 x8) => {| unwrap_sprop := Original_LF__DOT__Imp_LF_Imp_empty__st_iso hx2 |})
                             Original_LF__DOT__Imp_LF_Imp_X_iso 2 (imported_S (imported_S imported_0)) {| unwrap_sprop := S_iso (S_iso _0_iso) |} hx1)
                    |})
                   Original_LF__DOT__Imp_LF_Imp_Y_iso 1 (imported_S imported_0) {| unwrap_sprop := S_iso _0_iso |} hx0))
             x1 (fun H : imported_String_string => x2 H) (fun (x3 : String.string) (x4 : imported_String_string) (hx0 : rel_iso String_string_iso x3 x4) => IsoUnFunND hx hx0));
      from :=
        from
          (ex_iso
             (fun s' : Original.LF_DOT_Imp.LF.Imp.state =>
              Original.LF_DOT_Auto.LF.Auto.Repeat.ceval
                (Original.LF_DOT_Auto.LF.Auto.Repeat.CIf
                   (Original.LF_DOT_Imp.LF.Imp.BLe (Original.LF_DOT_Imp.LF.Imp.AId Original.LF_DOT_Imp.LF.Imp.X) (Original.LF_DOT_Imp.LF.Imp.AId Original.LF_DOT_Imp.LF.Imp.Y))
                   (Original.LF_DOT_Auto.LF.Auto.Repeat.CAsgn Original.LF_DOT_Imp.LF.Imp.Z
                      (Original.LF_DOT_Imp.LF.Imp.AMinus (Original.LF_DOT_Imp.LF.Imp.AId Original.LF_DOT_Imp.LF.Imp.Y) (Original.LF_DOT_Imp.LF.Imp.AId Original.LF_DOT_Imp.LF.Imp.X)))
                   (Original.LF_DOT_Auto.LF.Auto.Repeat.CAsgn Original.LF_DOT_Imp.LF.Imp.Y
                      (Original.LF_DOT_Imp.LF.Imp.APlus (Original.LF_DOT_Imp.LF.Imp.AId Original.LF_DOT_Imp.LF.Imp.X) (Original.LF_DOT_Imp.LF.Imp.AId Original.LF_DOT_Imp.LF.Imp.Z))))
                (Original.LF_DOT_Maps.LF.Maps.t_update (Original.LF_DOT_Maps.LF.Maps.t_update Original.LF_DOT_Imp.LF.Imp.empty_st Original.LF_DOT_Imp.LF.Imp.X 2) Original.LF_DOT_Imp.LF.Imp.Y 1) s')
             (fun H : imported_String_string -> imported_nat =>
              imported_Original_LF__DOT__Auto_LF_Auto_Repeat_ceval
                (imported_Original_LF__DOT__Auto_LF_Auto_Repeat_CIf
                   (imported_Original_LF__DOT__Imp_LF_Imp_BLe (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_X)
                      (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_Y))
                   (imported_Original_LF__DOT__Auto_LF_Auto_Repeat_CAsgn imported_Original_LF__DOT__Imp_LF_Imp_Z
                      (imported_Original_LF__DOT__Imp_LF_Imp_AMinus (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_Y)
                         (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_X)))
                   (imported_Original_LF__DOT__Auto_LF_Auto_Repeat_CAsgn imported_Original_LF__DOT__Imp_LF_Imp_Y
                      (imported_Original_LF__DOT__Imp_LF_Imp_APlus (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_X)
                         (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_Z))))
                (fun H0 : imported_String_string =>
                 imported_Original_LF__DOT__Maps_LF_Maps_t__update
                   (fun H1 : imported_String_string =>
                    imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun H2 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st H2) imported_Original_LF__DOT__Imp_LF_Imp_X
                      (imported_S (imported_S imported_0)) H1)
                   imported_Original_LF__DOT__Imp_LF_Imp_Y (imported_S imported_0) H0)
                (fun H0 : imported_String_string => H H0))
             (fun (x1 : Original.LF_DOT_Imp.LF.Imp.state) (x2 : imported_String_string -> imported_nat) (hx : rel_iso (IsoArrow String_string_iso nat_iso) x1 x2) =>
              Original_LF__DOT__Auto_LF_Auto_Repeat_ceval_iso
                (Original_LF__DOT__Auto_LF_Auto_Repeat_CIf_iso
                   (Original_LF__DOT__Imp_LF_Imp_BLe_iso (Original_LF__DOT__Imp_LF_Imp_AId_iso Original_LF__DOT__Imp_LF_Imp_X_iso)
                      (Original_LF__DOT__Imp_LF_Imp_AId_iso Original_LF__DOT__Imp_LF_Imp_Y_iso))
                   (Original_LF__DOT__Auto_LF_Auto_Repeat_CAsgn_iso Original_LF__DOT__Imp_LF_Imp_Z_iso
                      (Original_LF__DOT__Imp_LF_Imp_AMinus_iso (Original_LF__DOT__Imp_LF_Imp_AId_iso Original_LF__DOT__Imp_LF_Imp_Y_iso)
                         (Original_LF__DOT__Imp_LF_Imp_AId_iso Original_LF__DOT__Imp_LF_Imp_X_iso)))
                   (Original_LF__DOT__Auto_LF_Auto_Repeat_CAsgn_iso Original_LF__DOT__Imp_LF_Imp_Y_iso
                      (Original_LF__DOT__Imp_LF_Imp_APlus_iso (Original_LF__DOT__Imp_LF_Imp_AId_iso Original_LF__DOT__Imp_LF_Imp_X_iso)
                         (Original_LF__DOT__Imp_LF_Imp_AId_iso Original_LF__DOT__Imp_LF_Imp_Z_iso))))
                (Original.LF_DOT_Maps.LF.Maps.t_update (Original.LF_DOT_Maps.LF.Maps.t_update Original.LF_DOT_Imp.LF.Imp.empty_st Original.LF_DOT_Imp.LF.Imp.X 2) Original.LF_DOT_Imp.LF.Imp.Y 1)
                (fun H : imported_String_string =>
                 imported_Original_LF__DOT__Maps_LF_Maps_t__update
                   (fun H0 : imported_String_string =>
                    imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun H1 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st H1) imported_Original_LF__DOT__Imp_LF_Imp_X
                      (imported_S (imported_S imported_0)) H0)
                   imported_Original_LF__DOT__Imp_LF_Imp_Y (imported_S imported_0) H)
                (fun (x3 : String.string) (x4 : imported_String_string) (hx0 : rel_iso String_string_iso x3 x4) =>
                 unwrap_sprop
                   (Original_LF__DOT__Maps_LF_Maps_t__update_iso nat_iso (Original.LF_DOT_Maps.LF.Maps.t_update Original.LF_DOT_Imp.LF.Imp.empty_st Original.LF_DOT_Imp.LF.Imp.X 2)
                      (fun H : imported_String_string =>
                       imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun H0 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st H0)
                         imported_Original_LF__DOT__Imp_LF_Imp_X (imported_S (imported_S imported_0)) H)
                      (fun (x5 : String.string) (x6 : imported_String_string) (hx1 : rel_iso String_string_iso x5 x6) =>
                       {|
                         unwrap_sprop :=
                           unwrap_sprop
                             (Original_LF__DOT__Maps_LF_Maps_t__update_iso nat_iso Original.LF_DOT_Imp.LF.Imp.empty_st
                                (fun H : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st H)
                                (fun (x7 : String.string) (x8 : imported_String_string) (hx2 : rel_iso String_string_iso x7 x8) => {| unwrap_sprop := Original_LF__DOT__Imp_LF_Imp_empty__st_iso hx2 |})
                                Original_LF__DOT__Imp_LF_Imp_X_iso 2 (imported_S (imported_S imported_0)) {| unwrap_sprop := S_iso (S_iso _0_iso) |} hx1)
                       |})
                      Original_LF__DOT__Imp_LF_Imp_Y_iso 1 (imported_S imported_0) {| unwrap_sprop := S_iso _0_iso |} hx0))
                x1 (fun H : imported_String_string => x2 H) (fun (x3 : String.string) (x4 : imported_String_string) (hx0 : rel_iso String_string_iso x3 x4) => IsoUnFunND hx hx0)));
      to_from :=
        fun
          x : imported_ex
                (fun H : imported_String_string -> imported_nat =>
                 imported_Original_LF__DOT__Auto_LF_Auto_Repeat_ceval
                   (imported_Original_LF__DOT__Auto_LF_Auto_Repeat_CIf
                      (imported_Original_LF__DOT__Imp_LF_Imp_BLe (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_X)
                         (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_Y))
                      (imported_Original_LF__DOT__Auto_LF_Auto_Repeat_CAsgn imported_Original_LF__DOT__Imp_LF_Imp_Z
                         (imported_Original_LF__DOT__Imp_LF_Imp_AMinus (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_Y)
                            (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_X)))
                      (imported_Original_LF__DOT__Auto_LF_Auto_Repeat_CAsgn imported_Original_LF__DOT__Imp_LF_Imp_Y
                         (imported_Original_LF__DOT__Imp_LF_Imp_APlus (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_X)
                            (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_Z))))
                   (fun H0 : imported_String_string =>
                    imported_Original_LF__DOT__Maps_LF_Maps_t__update
                      (fun H1 : imported_String_string =>
                       imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun H2 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st H2)
                         imported_Original_LF__DOT__Imp_LF_Imp_X (imported_S (imported_S imported_0)) H1)
                      imported_Original_LF__DOT__Imp_LF_Imp_Y (imported_S imported_0) H0)
                   (fun H0 : imported_String_string => H H0)) =>
        to_from
          (ex_iso
             (fun s' : Original.LF_DOT_Imp.LF.Imp.state =>
              Original.LF_DOT_Auto.LF.Auto.Repeat.ceval
                (Original.LF_DOT_Auto.LF.Auto.Repeat.CIf
                   (Original.LF_DOT_Imp.LF.Imp.BLe (Original.LF_DOT_Imp.LF.Imp.AId Original.LF_DOT_Imp.LF.Imp.X) (Original.LF_DOT_Imp.LF.Imp.AId Original.LF_DOT_Imp.LF.Imp.Y))
                   (Original.LF_DOT_Auto.LF.Auto.Repeat.CAsgn Original.LF_DOT_Imp.LF.Imp.Z
                      (Original.LF_DOT_Imp.LF.Imp.AMinus (Original.LF_DOT_Imp.LF.Imp.AId Original.LF_DOT_Imp.LF.Imp.Y) (Original.LF_DOT_Imp.LF.Imp.AId Original.LF_DOT_Imp.LF.Imp.X)))
                   (Original.LF_DOT_Auto.LF.Auto.Repeat.CAsgn Original.LF_DOT_Imp.LF.Imp.Y
                      (Original.LF_DOT_Imp.LF.Imp.APlus (Original.LF_DOT_Imp.LF.Imp.AId Original.LF_DOT_Imp.LF.Imp.X) (Original.LF_DOT_Imp.LF.Imp.AId Original.LF_DOT_Imp.LF.Imp.Z))))
                (Original.LF_DOT_Maps.LF.Maps.t_update (Original.LF_DOT_Maps.LF.Maps.t_update Original.LF_DOT_Imp.LF.Imp.empty_st Original.LF_DOT_Imp.LF.Imp.X 2) Original.LF_DOT_Imp.LF.Imp.Y 1) s')
             (fun H : imported_String_string -> imported_nat =>
              imported_Original_LF__DOT__Auto_LF_Auto_Repeat_ceval
                (imported_Original_LF__DOT__Auto_LF_Auto_Repeat_CIf
                   (imported_Original_LF__DOT__Imp_LF_Imp_BLe (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_X)
                      (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_Y))
                   (imported_Original_LF__DOT__Auto_LF_Auto_Repeat_CAsgn imported_Original_LF__DOT__Imp_LF_Imp_Z
                      (imported_Original_LF__DOT__Imp_LF_Imp_AMinus (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_Y)
                         (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_X)))
                   (imported_Original_LF__DOT__Auto_LF_Auto_Repeat_CAsgn imported_Original_LF__DOT__Imp_LF_Imp_Y
                      (imported_Original_LF__DOT__Imp_LF_Imp_APlus (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_X)
                         (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_Z))))
                (fun H0 : imported_String_string =>
                 imported_Original_LF__DOT__Maps_LF_Maps_t__update
                   (fun H1 : imported_String_string =>
                    imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun H2 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st H2) imported_Original_LF__DOT__Imp_LF_Imp_X
                      (imported_S (imported_S imported_0)) H1)
                   imported_Original_LF__DOT__Imp_LF_Imp_Y (imported_S imported_0) H0)
                (fun H0 : imported_String_string => H H0))
             (fun (x1 : Original.LF_DOT_Imp.LF.Imp.state) (x2 : imported_String_string -> imported_nat) (hx : rel_iso (IsoArrow String_string_iso nat_iso) x1 x2) =>
              Original_LF__DOT__Auto_LF_Auto_Repeat_ceval_iso
                (Original_LF__DOT__Auto_LF_Auto_Repeat_CIf_iso
                   (Original_LF__DOT__Imp_LF_Imp_BLe_iso (Original_LF__DOT__Imp_LF_Imp_AId_iso Original_LF__DOT__Imp_LF_Imp_X_iso)
                      (Original_LF__DOT__Imp_LF_Imp_AId_iso Original_LF__DOT__Imp_LF_Imp_Y_iso))
                   (Original_LF__DOT__Auto_LF_Auto_Repeat_CAsgn_iso Original_LF__DOT__Imp_LF_Imp_Z_iso
                      (Original_LF__DOT__Imp_LF_Imp_AMinus_iso (Original_LF__DOT__Imp_LF_Imp_AId_iso Original_LF__DOT__Imp_LF_Imp_Y_iso)
                         (Original_LF__DOT__Imp_LF_Imp_AId_iso Original_LF__DOT__Imp_LF_Imp_X_iso)))
                   (Original_LF__DOT__Auto_LF_Auto_Repeat_CAsgn_iso Original_LF__DOT__Imp_LF_Imp_Y_iso
                      (Original_LF__DOT__Imp_LF_Imp_APlus_iso (Original_LF__DOT__Imp_LF_Imp_AId_iso Original_LF__DOT__Imp_LF_Imp_X_iso)
                         (Original_LF__DOT__Imp_LF_Imp_AId_iso Original_LF__DOT__Imp_LF_Imp_Z_iso))))
                (Original.LF_DOT_Maps.LF.Maps.t_update (Original.LF_DOT_Maps.LF.Maps.t_update Original.LF_DOT_Imp.LF.Imp.empty_st Original.LF_DOT_Imp.LF.Imp.X 2) Original.LF_DOT_Imp.LF.Imp.Y 1)
                (fun H : imported_String_string =>
                 imported_Original_LF__DOT__Maps_LF_Maps_t__update
                   (fun H0 : imported_String_string =>
                    imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun H1 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st H1) imported_Original_LF__DOT__Imp_LF_Imp_X
                      (imported_S (imported_S imported_0)) H0)
                   imported_Original_LF__DOT__Imp_LF_Imp_Y (imported_S imported_0) H)
                (fun (x3 : String.string) (x4 : imported_String_string) (hx0 : rel_iso String_string_iso x3 x4) =>
                 unwrap_sprop
                   (Original_LF__DOT__Maps_LF_Maps_t__update_iso nat_iso (Original.LF_DOT_Maps.LF.Maps.t_update Original.LF_DOT_Imp.LF.Imp.empty_st Original.LF_DOT_Imp.LF.Imp.X 2)
                      (fun H : imported_String_string =>
                       imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun H0 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st H0)
                         imported_Original_LF__DOT__Imp_LF_Imp_X (imported_S (imported_S imported_0)) H)
                      (fun (x5 : String.string) (x6 : imported_String_string) (hx1 : rel_iso String_string_iso x5 x6) =>
                       {|
                         unwrap_sprop :=
                           unwrap_sprop
                             (Original_LF__DOT__Maps_LF_Maps_t__update_iso nat_iso Original.LF_DOT_Imp.LF.Imp.empty_st
                                (fun H : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st H)
                                (fun (x7 : String.string) (x8 : imported_String_string) (hx2 : rel_iso String_string_iso x7 x8) => {| unwrap_sprop := Original_LF__DOT__Imp_LF_Imp_empty__st_iso hx2 |})
                                Original_LF__DOT__Imp_LF_Imp_X_iso 2 (imported_S (imported_S imported_0)) {| unwrap_sprop := S_iso (S_iso _0_iso) |} hx1)
                       |})
                      Original_LF__DOT__Imp_LF_Imp_Y_iso 1 (imported_S imported_0) {| unwrap_sprop := S_iso _0_iso |} hx0))
                x1 (fun H : imported_String_string => x2 H) (fun (x3 : String.string) (x4 : imported_String_string) (hx0 : rel_iso String_string_iso x3 x4) => IsoUnFunND hx hx0)))
          x;
      from_to :=
        fun
          x : exists y : Original.LF_DOT_Imp.LF.Imp.state,
                Original.LF_DOT_Auto.LF.Auto.Repeat.ceval
                  (Original.LF_DOT_Auto.LF.Auto.Repeat.CIf
                     (Original.LF_DOT_Imp.LF.Imp.BLe (Original.LF_DOT_Imp.LF.Imp.AId Original.LF_DOT_Imp.LF.Imp.X) (Original.LF_DOT_Imp.LF.Imp.AId Original.LF_DOT_Imp.LF.Imp.Y))
                     (Original.LF_DOT_Auto.LF.Auto.Repeat.CAsgn Original.LF_DOT_Imp.LF.Imp.Z
                        (Original.LF_DOT_Imp.LF.Imp.AMinus (Original.LF_DOT_Imp.LF.Imp.AId Original.LF_DOT_Imp.LF.Imp.Y) (Original.LF_DOT_Imp.LF.Imp.AId Original.LF_DOT_Imp.LF.Imp.X)))
                     (Original.LF_DOT_Auto.LF.Auto.Repeat.CAsgn Original.LF_DOT_Imp.LF.Imp.Y
                        (Original.LF_DOT_Imp.LF.Imp.APlus (Original.LF_DOT_Imp.LF.Imp.AId Original.LF_DOT_Imp.LF.Imp.X) (Original.LF_DOT_Imp.LF.Imp.AId Original.LF_DOT_Imp.LF.Imp.Z))))
                  (Original.LF_DOT_Maps.LF.Maps.t_update (Original.LF_DOT_Maps.LF.Maps.t_update Original.LF_DOT_Imp.LF.Imp.empty_st Original.LF_DOT_Imp.LF.Imp.X 2) Original.LF_DOT_Imp.LF.Imp.Y 1) y =>
        seq_p_of_t
          (from_to
             (ex_iso
                (fun s' : Original.LF_DOT_Imp.LF.Imp.state =>
                 Original.LF_DOT_Auto.LF.Auto.Repeat.ceval
                   (Original.LF_DOT_Auto.LF.Auto.Repeat.CIf
                      (Original.LF_DOT_Imp.LF.Imp.BLe (Original.LF_DOT_Imp.LF.Imp.AId Original.LF_DOT_Imp.LF.Imp.X) (Original.LF_DOT_Imp.LF.Imp.AId Original.LF_DOT_Imp.LF.Imp.Y))
                      (Original.LF_DOT_Auto.LF.Auto.Repeat.CAsgn Original.LF_DOT_Imp.LF.Imp.Z
                         (Original.LF_DOT_Imp.LF.Imp.AMinus (Original.LF_DOT_Imp.LF.Imp.AId Original.LF_DOT_Imp.LF.Imp.Y) (Original.LF_DOT_Imp.LF.Imp.AId Original.LF_DOT_Imp.LF.Imp.X)))
                      (Original.LF_DOT_Auto.LF.Auto.Repeat.CAsgn Original.LF_DOT_Imp.LF.Imp.Y
                         (Original.LF_DOT_Imp.LF.Imp.APlus (Original.LF_DOT_Imp.LF.Imp.AId Original.LF_DOT_Imp.LF.Imp.X) (Original.LF_DOT_Imp.LF.Imp.AId Original.LF_DOT_Imp.LF.Imp.Z))))
                   (Original.LF_DOT_Maps.LF.Maps.t_update (Original.LF_DOT_Maps.LF.Maps.t_update Original.LF_DOT_Imp.LF.Imp.empty_st Original.LF_DOT_Imp.LF.Imp.X 2) Original.LF_DOT_Imp.LF.Imp.Y 1) s')
                (fun H : imported_String_string -> imported_nat =>
                 imported_Original_LF__DOT__Auto_LF_Auto_Repeat_ceval
                   (imported_Original_LF__DOT__Auto_LF_Auto_Repeat_CIf
                      (imported_Original_LF__DOT__Imp_LF_Imp_BLe (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_X)
                         (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_Y))
                      (imported_Original_LF__DOT__Auto_LF_Auto_Repeat_CAsgn imported_Original_LF__DOT__Imp_LF_Imp_Z
                         (imported_Original_LF__DOT__Imp_LF_Imp_AMinus (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_Y)
                            (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_X)))
                      (imported_Original_LF__DOT__Auto_LF_Auto_Repeat_CAsgn imported_Original_LF__DOT__Imp_LF_Imp_Y
                         (imported_Original_LF__DOT__Imp_LF_Imp_APlus (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_X)
                            (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_Z))))
                   (fun H0 : imported_String_string =>
                    imported_Original_LF__DOT__Maps_LF_Maps_t__update
                      (fun H1 : imported_String_string =>
                       imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun H2 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st H2)
                         imported_Original_LF__DOT__Imp_LF_Imp_X (imported_S (imported_S imported_0)) H1)
                      imported_Original_LF__DOT__Imp_LF_Imp_Y (imported_S imported_0) H0)
                   (fun H0 : imported_String_string => H H0))
                (fun (x1 : Original.LF_DOT_Imp.LF.Imp.state) (x2 : imported_String_string -> imported_nat) (hx : rel_iso (IsoArrow String_string_iso nat_iso) x1 x2) =>
                 Original_LF__DOT__Auto_LF_Auto_Repeat_ceval_iso
                   (Original_LF__DOT__Auto_LF_Auto_Repeat_CIf_iso
                      (Original_LF__DOT__Imp_LF_Imp_BLe_iso (Original_LF__DOT__Imp_LF_Imp_AId_iso Original_LF__DOT__Imp_LF_Imp_X_iso)
                         (Original_LF__DOT__Imp_LF_Imp_AId_iso Original_LF__DOT__Imp_LF_Imp_Y_iso))
                      (Original_LF__DOT__Auto_LF_Auto_Repeat_CAsgn_iso Original_LF__DOT__Imp_LF_Imp_Z_iso
                         (Original_LF__DOT__Imp_LF_Imp_AMinus_iso (Original_LF__DOT__Imp_LF_Imp_AId_iso Original_LF__DOT__Imp_LF_Imp_Y_iso)
                            (Original_LF__DOT__Imp_LF_Imp_AId_iso Original_LF__DOT__Imp_LF_Imp_X_iso)))
                      (Original_LF__DOT__Auto_LF_Auto_Repeat_CAsgn_iso Original_LF__DOT__Imp_LF_Imp_Y_iso
                         (Original_LF__DOT__Imp_LF_Imp_APlus_iso (Original_LF__DOT__Imp_LF_Imp_AId_iso Original_LF__DOT__Imp_LF_Imp_X_iso)
                            (Original_LF__DOT__Imp_LF_Imp_AId_iso Original_LF__DOT__Imp_LF_Imp_Z_iso))))
                   (Original.LF_DOT_Maps.LF.Maps.t_update (Original.LF_DOT_Maps.LF.Maps.t_update Original.LF_DOT_Imp.LF.Imp.empty_st Original.LF_DOT_Imp.LF.Imp.X 2) Original.LF_DOT_Imp.LF.Imp.Y 1)
                   (fun H : imported_String_string =>
                    imported_Original_LF__DOT__Maps_LF_Maps_t__update
                      (fun H0 : imported_String_string =>
                       imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun H1 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st H1)
                         imported_Original_LF__DOT__Imp_LF_Imp_X (imported_S (imported_S imported_0)) H0)
                      imported_Original_LF__DOT__Imp_LF_Imp_Y (imported_S imported_0) H)
                   (fun (x3 : String.string) (x4 : imported_String_string) (hx0 : rel_iso String_string_iso x3 x4) =>
                    unwrap_sprop
                      (Original_LF__DOT__Maps_LF_Maps_t__update_iso nat_iso (Original.LF_DOT_Maps.LF.Maps.t_update Original.LF_DOT_Imp.LF.Imp.empty_st Original.LF_DOT_Imp.LF.Imp.X 2)
                         (fun H : imported_String_string =>
                          imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun H0 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st H0)
                            imported_Original_LF__DOT__Imp_LF_Imp_X (imported_S (imported_S imported_0)) H)
                         (fun (x5 : String.string) (x6 : imported_String_string) (hx1 : rel_iso String_string_iso x5 x6) =>
                          {|
                            unwrap_sprop :=
                              unwrap_sprop
                                (Original_LF__DOT__Maps_LF_Maps_t__update_iso nat_iso Original.LF_DOT_Imp.LF.Imp.empty_st
                                   (fun H : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st H)
                                   (fun (x7 : String.string) (x8 : imported_String_string) (hx2 : rel_iso String_string_iso x7 x8) =>
                                    {| unwrap_sprop := Original_LF__DOT__Imp_LF_Imp_empty__st_iso hx2 |})
                                   Original_LF__DOT__Imp_LF_Imp_X_iso 2 (imported_S (imported_S imported_0)) {| unwrap_sprop := S_iso (S_iso _0_iso) |} hx1)
                          |})
                         Original_LF__DOT__Imp_LF_Imp_Y_iso 1 (imported_S imported_0) {| unwrap_sprop := S_iso _0_iso |} hx0))
                   x1 (fun H : imported_String_string => x2 H) (fun (x3 : String.string) (x4 : imported_String_string) (hx0 : rel_iso String_string_iso x3 x4) => IsoUnFunND hx hx0)))
             x)
    |} Original.LF_DOT_Auto.LF.Auto.eauto_example imported_Original_LF__DOT__Auto_LF_Auto_eauto__example.
Existing Instance Original_LF__DOT__Auto_LF_Auto_eauto__example_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Auto.LF.Auto.eauto_example ?x) => unify x Original_LF__DOT__Auto_LF_Auto_eauto__example_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Auto.LF.Auto.eauto_example imported_Original_LF__DOT__Auto_LF_Auto_eauto__example ?x) => unify x Original_LF__DOT__Auto_LF_Auto_eauto__example_iso; constructor : typeclass_instances.


End Interface.