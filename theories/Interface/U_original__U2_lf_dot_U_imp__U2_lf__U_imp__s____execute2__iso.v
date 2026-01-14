From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__sinstr__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_smult__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_splus__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_sload__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_x__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.false__iso Interface.list__iso Interface.cons__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_spush__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__empty____st__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__s____execute__iso Interface.U_s__iso Interface.__0__iso Interface.nil__iso Interface.true__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__sinstr__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_smult__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_splus__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_sload__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_x__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.false__iso Interface.list__iso Interface.cons__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_spush__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__empty____st__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__s____execute__iso Interface.U_s__iso Interface.__0__iso Interface.nil__iso Interface.true__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__sinstr__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_smult__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_splus__iso.CodeBlocks Interface.U_string__string__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_sload__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_x__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update__iso.CodeBlocks Interface.U_string__U_emptyU_string__iso.CodeBlocks Interface.U_string__U_string__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.bool__iso.CodeBlocks Interface.U_ascii__U_ascii__iso.CodeBlocks Interface.false__iso.CodeBlocks Interface.list__iso.CodeBlocks Interface.cons__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_spush__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__empty____st__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__s____execute__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks Interface.nil__iso.CodeBlocks Interface.true__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__sinstr__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_smult__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_splus__iso.Interface <+ Interface.U_string__string__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_sload__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_x__iso.Interface <+ Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.Interface <+ Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update__iso.Interface <+ Interface.U_string__U_emptyU_string__iso.Interface <+ Interface.U_string__U_string__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.bool__iso.Interface <+ Interface.U_ascii__U_ascii__iso.Interface <+ Interface.false__iso.Interface <+ Interface.list__iso.Interface <+ Interface.cons__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U2_spush__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__empty____st__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__s____execute__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface <+ Interface.nil__iso.Interface <+ Interface.true__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Imp_LF_Imp_s__execute2 : imported_Corelib_Init_Logic_eq
    (imported_Original_LF__DOT__Imp_LF_Imp_s__execute
       (fun x : imported_String_string =>
        imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun x0 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st x0) imported_Original_LF__DOT__Imp_LF_Imp_X
          (imported_S (imported_S (imported_S imported_0))) x)
       (imported_cons (imported_S (imported_S (imported_S imported_0))) (imported_cons (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0)))) (imported_nil imported_nat)))
       (imported_cons (imported_Original_LF__DOT__Imp_LF_Imp_SPush (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0)))))
          (imported_cons (imported_Original_LF__DOT__Imp_LF_Imp_SLoad imported_Original_LF__DOT__Imp_LF_Imp_X)
             (imported_cons imported_Original_LF__DOT__Imp_LF_Imp_SMult (imported_cons imported_Original_LF__DOT__Imp_LF_Imp_SPlus (imported_nil imported_Original_LF__DOT__Imp_LF_Imp_sinstr))))))
    (imported_cons (imported_S (imported_S (imported_S (iterate1 imported_S 12 imported_0))))
       (imported_cons (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0)))) (imported_nil imported_nat))).
Parameter Original_LF__DOT__Imp_LF_Imp_s__execute2_iso : rel_iso
    (Corelib_Init_Logic_eq_iso
       (Original_LF__DOT__Imp_LF_Imp_s__execute_iso (Original.LF_DOT_Maps.LF.Maps.t_update Original.LF_DOT_Imp.LF.Imp.empty_st Original.LF_DOT_Imp.LF.Imp.X 3)
          (fun x : imported_String_string =>
           imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun x0 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st x0) imported_Original_LF__DOT__Imp_LF_Imp_X
             (imported_S (imported_S (imported_S imported_0))) x)
          (fun (x1 : String.string) (x2 : imported_String_string) (hx : rel_iso String_string_iso x1 x2) =>
           unwrap_sprop
             (Original_LF__DOT__Maps_LF_Maps_t__update_iso nat_iso Original.LF_DOT_Imp.LF.Imp.empty_st (fun x : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st x)
                (fun (x3 : String.string) (x4 : imported_String_string) (hx0 : rel_iso String_string_iso x3 x4) => {| unwrap_sprop := Original_LF__DOT__Imp_LF_Imp_empty__st_iso hx0 |})
                Original_LF__DOT__Imp_LF_Imp_X_iso 3 (imported_S (imported_S (imported_S imported_0))) {| unwrap_sprop := S_iso (S_iso (S_iso _0_iso)) |} hx))
          (cons_iso (S_iso (S_iso (S_iso _0_iso))) (cons_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 1 0 imported_0 _0_iso)))) (nil_iso nat_iso)))
          (cons_iso (Original_LF__DOT__Imp_LF_Imp_SPush_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 1 0 imported_0 _0_iso)))))
             (cons_iso (Original_LF__DOT__Imp_LF_Imp_SLoad_iso Original_LF__DOT__Imp_LF_Imp_X_iso)
                (cons_iso Original_LF__DOT__Imp_LF_Imp_SMult_iso (cons_iso Original_LF__DOT__Imp_LF_Imp_SPlus_iso (nil_iso Original_LF__DOT__Imp_LF_Imp_sinstr_iso))))))
       (cons_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 12 0 imported_0 _0_iso))))
          (cons_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 1 0 imported_0 _0_iso)))) (nil_iso nat_iso))))
    Original.LF_DOT_Imp.LF.Imp.s_execute2 imported_Original_LF__DOT__Imp_LF_Imp_s__execute2.
Existing Instance Original_LF__DOT__Imp_LF_Imp_s__execute2_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.s_execute2 ?x) => unify x Original_LF__DOT__Imp_LF_Imp_s__execute2_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.s_execute2 imported_Original_LF__DOT__Imp_LF_Imp_s__execute2 ?x) => unify x Original_LF__DOT__Imp_LF_Imp_s__execute2_iso; constructor : typeclass_instances.


End Interface.