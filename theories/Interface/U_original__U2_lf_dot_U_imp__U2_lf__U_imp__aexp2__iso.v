From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_amult__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aplus__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aid__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_x__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_y__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_z__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.false__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__empty____st__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aeval__iso Interface.U_s__iso Interface.__0__iso Interface.true__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_amult__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aplus__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aid__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_x__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_y__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_z__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.false__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__empty____st__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aeval__iso Interface.U_s__iso Interface.__0__iso Interface.true__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_amult__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aplus__iso.CodeBlocks Interface.U_string__string__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aid__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_x__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_y__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_z__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update__iso.CodeBlocks Interface.U_string__U_emptyU_string__iso.CodeBlocks Interface.U_string__U_string__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.bool__iso.CodeBlocks Interface.U_ascii__U_ascii__iso.CodeBlocks Interface.false__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__empty____st__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aeval__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks Interface.true__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_amult__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aplus__iso.Interface <+ Interface.U_string__string__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_aid__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_x__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_y__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_z__iso.Interface <+ Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.Interface <+ Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update__iso.Interface <+ Interface.U_string__U_emptyU_string__iso.Interface <+ Interface.U_string__U_string__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.bool__iso.Interface <+ Interface.U_ascii__U_ascii__iso.Interface <+ Interface.false__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__empty____st__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aeval__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface <+ Interface.true__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Imp_LF_Imp_aexp2 : imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Imp_LF_Imp_aeval
       (fun x : imported_String_string =>
        imported_Original_LF__DOT__Maps_LF_Maps_t__update
          (fun x0 : imported_String_string =>
           imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun x1 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st x1) imported_Original_LF__DOT__Imp_LF_Imp_Y
             (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0)))) x0)
          imported_Original_LF__DOT__Imp_LF_Imp_X (imported_S (imported_S (imported_S (iterate1 imported_S 2 imported_0)))) x)
       (imported_Original_LF__DOT__Imp_LF_Imp_APlus (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_Z)
          (imported_Original_LF__DOT__Imp_LF_Imp_AMult (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_X)
             (imported_Original_LF__DOT__Imp_LF_Imp_AId imported_Original_LF__DOT__Imp_LF_Imp_Y))))
    (imported_S (imported_S (imported_S (iterate1 imported_S 17 imported_0)))).
Parameter Original_LF__DOT__Imp_LF_Imp_aexp2_iso : rel_iso
    (Corelib_Init_Logic_eq_iso
       (Original_LF__DOT__Imp_LF_Imp_aeval_iso
          (Original.LF_DOT_Maps.LF.Maps.t_update (Original.LF_DOT_Maps.LF.Maps.t_update Original.LF_DOT_Imp.LF.Imp.empty_st Original.LF_DOT_Imp.LF.Imp.Y 4) Original.LF_DOT_Imp.LF.Imp.X 5)
          (fun x : imported_String_string =>
           imported_Original_LF__DOT__Maps_LF_Maps_t__update
             (fun x0 : imported_String_string =>
              imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun x1 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st x1) imported_Original_LF__DOT__Imp_LF_Imp_Y
                (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0)))) x0)
             imported_Original_LF__DOT__Imp_LF_Imp_X (imported_S (imported_S (imported_S (iterate1 imported_S 2 imported_0)))) x)
          (fun (x1 : String.string) (x2 : imported_String_string) (hx : rel_iso String_string_iso x1 x2) =>
           unwrap_sprop
             (Original_LF__DOT__Maps_LF_Maps_t__update_iso nat_iso (Original.LF_DOT_Maps.LF.Maps.t_update Original.LF_DOT_Imp.LF.Imp.empty_st Original.LF_DOT_Imp.LF.Imp.Y 4)
                (fun x : imported_String_string =>
                 imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun x0 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st x0) imported_Original_LF__DOT__Imp_LF_Imp_Y
                   (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0)))) x)
                (fun (x3 : String.string) (x4 : imported_String_string) (hx0 : rel_iso String_string_iso x3 x4) =>
                 {|
                   unwrap_sprop :=
                     unwrap_sprop
                       (Original_LF__DOT__Maps_LF_Maps_t__update_iso nat_iso Original.LF_DOT_Imp.LF.Imp.empty_st (fun x : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st x)
                          (fun (x5 : String.string) (x6 : imported_String_string) (hx1 : rel_iso String_string_iso x5 x6) => {| unwrap_sprop := Original_LF__DOT__Imp_LF_Imp_empty__st_iso hx1 |})
                          Original_LF__DOT__Imp_LF_Imp_Y_iso 4 (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0))))
                          {| unwrap_sprop := S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 1 0 imported_0 _0_iso))) |} hx0)
                 |})
                Original_LF__DOT__Imp_LF_Imp_X_iso 5 (imported_S (imported_S (imported_S (iterate1 imported_S 2 imported_0))))
                {| unwrap_sprop := S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 2 0 imported_0 _0_iso))) |} hx))
          (Original_LF__DOT__Imp_LF_Imp_APlus_iso (Original_LF__DOT__Imp_LF_Imp_AId_iso Original_LF__DOT__Imp_LF_Imp_Z_iso)
             (Original_LF__DOT__Imp_LF_Imp_AMult_iso (Original_LF__DOT__Imp_LF_Imp_AId_iso Original_LF__DOT__Imp_LF_Imp_X_iso)
                (Original_LF__DOT__Imp_LF_Imp_AId_iso Original_LF__DOT__Imp_LF_Imp_Y_iso))))
       (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 17 0 imported_0 _0_iso)))))
    Original.LF_DOT_Imp.LF.Imp.aexp2 imported_Original_LF__DOT__Imp_LF_Imp_aexp2.
Existing Instance Original_LF__DOT__Imp_LF_Imp_aexp2_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.aexp2 ?x) => unify x Original_LF__DOT__Imp_LF_Imp_aexp2_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.aexp2 imported_Original_LF__DOT__Imp_LF_Imp_aexp2 ?x) => unify x Original_LF__DOT__Imp_LF_Imp_aexp2_iso; constructor : typeclass_instances.


End Interface.