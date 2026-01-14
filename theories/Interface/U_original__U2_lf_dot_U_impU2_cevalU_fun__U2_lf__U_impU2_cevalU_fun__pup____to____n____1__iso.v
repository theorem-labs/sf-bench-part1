From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso Interface.U_original__U2_lf_dot_U_impU2_cevalU_fun__U2_lf__U_impU2_cevalU_fun__pup____to____n__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_x__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.false__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__empty____st__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso Interface.U_s__iso Interface.__0__iso Interface.option__iso Interface.U_some__iso Interface.prod__iso Interface.U_original__U2_lf_dot_U_impU2_cevalU_fun__U2_lf__U_impU2_cevalU_fun__test____ceval__iso Interface.pair__iso Interface.true__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso Interface.U_original__U2_lf_dot_U_impU2_cevalU_fun__U2_lf__U_impU2_cevalU_fun__pup____to____n__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_x__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.false__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__empty____st__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso Interface.U_s__iso Interface.__0__iso Interface.option__iso Interface.U_some__iso Interface.prod__iso Interface.U_original__U2_lf_dot_U_impU2_cevalU_fun__U2_lf__U_impU2_cevalU_fun__test____ceval__iso Interface.pair__iso Interface.true__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_impU2_cevalU_fun__U2_lf__U_impU2_cevalU_fun__pup____to____n__iso.CodeBlocks Interface.U_string__string__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_x__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update__iso.CodeBlocks Interface.U_string__U_emptyU_string__iso.CodeBlocks Interface.U_string__U_string__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.bool__iso.CodeBlocks Interface.U_ascii__U_ascii__iso.CodeBlocks Interface.false__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__empty____st__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks Interface.option__iso.CodeBlocks Interface.U_some__iso.CodeBlocks Interface.prod__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_impU2_cevalU_fun__U2_lf__U_impU2_cevalU_fun__test____ceval__iso.CodeBlocks Interface.pair__iso.CodeBlocks Interface.true__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso.Interface <+ Interface.U_original__U2_lf_dot_U_impU2_cevalU_fun__U2_lf__U_impU2_cevalU_fun__pup____to____n__iso.Interface <+ Interface.U_string__string__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_x__iso.Interface <+ Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.Interface <+ Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update__iso.Interface <+ Interface.U_string__U_emptyU_string__iso.Interface <+ Interface.U_string__U_string__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.bool__iso.Interface <+ Interface.U_ascii__U_ascii__iso.Interface <+ Interface.false__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__empty____st__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface <+ Interface.option__iso.Interface <+ Interface.U_some__iso.Interface <+ Interface.prod__iso.Interface <+ Interface.U_original__U2_lf_dot_U_impU2_cevalU_fun__U2_lf__U_impU2_cevalU_fun__test____ceval__iso.Interface <+ Interface.pair__iso.Interface <+ Interface.true__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_pup__to__n__1 : imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_test__ceval
       (fun x : imported_String_string =>
        imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun x0 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st x0) imported_Original_LF__DOT__Imp_LF_Imp_X
          (imported_S (imported_S (imported_S (iterate1 imported_S 2 imported_0)))) x)
       imported_Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_pup__to__n)
    (imported_Some (imported_pair (imported_pair imported_0 (imported_S (imported_S (imported_S (iterate1 imported_S 12 imported_0))))) imported_0)).
Parameter Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_pup__to__n__1_iso : rel_iso
    (Corelib_Init_Logic_eq_iso
       (Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_test__ceval_iso (Original.LF_DOT_Maps.LF.Maps.t_update Original.LF_DOT_Imp.LF.Imp.empty_st Original.LF_DOT_Imp.LF.Imp.X 5)
          (fun x : imported_String_string =>
           imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun x0 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st x0) imported_Original_LF__DOT__Imp_LF_Imp_X
             (imported_S (imported_S (imported_S (iterate1 imported_S 2 imported_0)))) x)
          (fun (x1 : String.string) (x2 : imported_String_string) (hx : rel_iso String_string_iso x1 x2) =>
           unwrap_sprop
             (Original_LF__DOT__Maps_LF_Maps_t__update_iso nat_iso Original.LF_DOT_Imp.LF.Imp.empty_st (fun x : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st x)
                (fun (x3 : String.string) (x4 : imported_String_string) (hx0 : rel_iso String_string_iso x3 x4) => {| unwrap_sprop := Original_LF__DOT__Imp_LF_Imp_empty__st_iso hx0 |})
                Original_LF__DOT__Imp_LF_Imp_X_iso 5 (imported_S (imported_S (imported_S (iterate1 imported_S 2 imported_0))))
                {| unwrap_sprop := S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 2 0 imported_0 _0_iso))) |} hx))
          Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_pup__to__n_iso)
       (Some_iso (pair_iso (pair_iso _0_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 12 0 imported_0 _0_iso))))) _0_iso)))
    Original.LF_DOT_ImpCEvalFun.LF.ImpCEvalFun.pup_to_n_1 imported_Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_pup__to__n__1.
Existing Instance Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_pup__to__n__1_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_ImpCEvalFun.LF.ImpCEvalFun.pup_to_n_1 ?x) => unify x Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_pup__to__n__1_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_ImpCEvalFun.LF.ImpCEvalFun.pup_to_n_1 imported_Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_pup__to__n__1 ?x) => unify x Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_pup__to__n__1_iso; constructor : typeclass_instances.


End Interface.