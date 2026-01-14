From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__sinstr__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.false__iso Interface.list__iso Interface.app__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__s____execute__iso Interface.true__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__sinstr__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.false__iso Interface.list__iso Interface.app__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__s____execute__iso Interface.true__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__sinstr__iso.CodeBlocks Interface.U_string__string__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.CodeBlocks Interface.U_string__U_emptyU_string__iso.CodeBlocks Interface.U_string__U_string__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.bool__iso.CodeBlocks Interface.U_ascii__U_ascii__iso.CodeBlocks Interface.false__iso.CodeBlocks Interface.list__iso.CodeBlocks Interface.app__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__s____execute__iso.CodeBlocks Interface.true__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__sinstr__iso.Interface <+ Interface.U_string__string__iso.Interface <+ Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.Interface <+ Interface.U_string__U_emptyU_string__iso.Interface <+ Interface.U_string__U_string__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.bool__iso.Interface <+ Interface.U_ascii__U_ascii__iso.Interface <+ Interface.false__iso.Interface <+ Interface.list__iso.Interface <+ Interface.app__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__s____execute__iso.Interface <+ Interface.true__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Imp_LF_Imp_execute__app : forall (x : imported_String_string -> imported_nat) (x0 x1 : imported_list imported_Original_LF__DOT__Imp_LF_Imp_sinstr) (x2 : imported_list imported_nat),
  imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Imp_LF_Imp_s__execute (fun x3 : imported_String_string => x x3) x2 (imported_app x0 x1))
    (imported_Original_LF__DOT__Imp_LF_Imp_s__execute (fun x3 : imported_String_string => x x3) (imported_Original_LF__DOT__Imp_LF_Imp_s__execute (fun x3 : imported_String_string => x x3) x2 x0) x1).
Parameter Original_LF__DOT__Imp_LF_Imp_execute__app_iso : forall (x1 : Original.LF_DOT_Imp.LF.Imp.state) (x2 : imported_String_string -> imported_nat)
    (hx : forall (x3 : String.string) (x4 : imported_String_string), rel_iso String_string_iso x3 x4 -> rel_iso nat_iso (x1 x3) (x2 x4)) (x3 : list Original.LF_DOT_Imp.LF.Imp.sinstr)
    (x4 : imported_list imported_Original_LF__DOT__Imp_LF_Imp_sinstr) (hx0 : rel_iso (list_iso Original_LF__DOT__Imp_LF_Imp_sinstr_iso) x3 x4) (x5 : list Original.LF_DOT_Imp.LF.Imp.sinstr)
    (x6 : imported_list imported_Original_LF__DOT__Imp_LF_Imp_sinstr) (hx1 : rel_iso (list_iso Original_LF__DOT__Imp_LF_Imp_sinstr_iso) x5 x6) (x7 : list nat) (x8 : imported_list imported_nat)
    (hx2 : rel_iso (list_iso nat_iso) x7 x8),
  rel_iso
    (Corelib_Init_Logic_eq_iso
       (Original_LF__DOT__Imp_LF_Imp_s__execute_iso x1 (fun x : imported_String_string => x2 x)
          (fun (x9 : String.string) (x10 : imported_String_string) (hx3 : rel_iso String_string_iso x9 x10) => hx x9 x10 hx3) hx2 (app_iso hx0 hx1))
       (Original_LF__DOT__Imp_LF_Imp_s__execute_iso x1 (fun x : imported_String_string => x2 x)
          (fun (x9 : String.string) (x10 : imported_String_string) (hx3 : rel_iso String_string_iso x9 x10) => hx x9 x10 hx3)
          (Original_LF__DOT__Imp_LF_Imp_s__execute_iso x1 (fun x : imported_String_string => x2 x)
             (fun (x9 : String.string) (x10 : imported_String_string) (hx3 : rel_iso String_string_iso x9 x10) => hx x9 x10 hx3) hx2 hx0)
          hx1))
    (Original.LF_DOT_Imp.LF.Imp.execute_app x1 x3 x5 x7) (imported_Original_LF__DOT__Imp_LF_Imp_execute__app x2 x4 x6 x8).
Existing Instance Original_LF__DOT__Imp_LF_Imp_execute__app_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.execute_app ?x) => unify x Original_LF__DOT__Imp_LF_Imp_execute__app_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.execute_app imported_Original_LF__DOT__Imp_LF_Imp_execute__app ?x) => unify x Original_LF__DOT__Imp_LF_Imp_execute__app_iso; constructor : typeclass_instances.


End Interface.