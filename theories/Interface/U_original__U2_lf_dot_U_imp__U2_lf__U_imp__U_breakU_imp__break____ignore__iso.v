From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__com__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__U2_cbreak__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__U2_cseq__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__result__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.false__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__ceval__iso Interface.true__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__com__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__U2_cbreak__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__U2_cseq__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__result__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.false__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__ceval__iso Interface.true__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__com__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__U2_cbreak__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__U2_cseq__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__result__iso.CodeBlocks Interface.U_string__string__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.CodeBlocks Interface.U_string__U_emptyU_string__iso.CodeBlocks Interface.U_string__U_string__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.bool__iso.CodeBlocks Interface.U_ascii__U_ascii__iso.CodeBlocks Interface.false__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__ceval__iso.CodeBlocks Interface.true__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__com__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__U2_cbreak__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__U2_cseq__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__result__iso.Interface <+ Interface.U_string__string__iso.Interface <+ Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.Interface <+ Interface.U_string__U_emptyU_string__iso.Interface <+ Interface.U_string__U_string__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.bool__iso.Interface <+ Interface.U_ascii__U_ascii__iso.Interface <+ Interface.false__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__ceval__iso.Interface <+ Interface.true__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_break__ignore : forall (x : imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_com) (x0 x1 : imported_String_string -> imported_nat) (x2 : imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_result),
  imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval (imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_CSeq imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_CBreak x)
    (fun x3 : imported_String_string => x0 x3) x2 (fun x3 : imported_String_string => x1 x3) ->
  imported_Corelib_Init_Logic_eq (fun x12 : imported_String_string => x0 x12) (fun x12 : imported_String_string => x1 x12).
Parameter Original_LF__DOT__Imp_LF_Imp_BreakImp_break__ignore_iso : forall (x1 : Original.LF_DOT_Imp.LF.Imp.BreakImp.com) (x2 : imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_com) (hx : rel_iso Original_LF__DOT__Imp_LF_Imp_BreakImp_com_iso x1 x2)
    (x3 : Original.LF_DOT_Imp.LF.Imp.state) (x4 : imported_String_string -> imported_nat)
    (hx0 : forall (x5 : String.string) (x6 : imported_String_string), rel_iso String_string_iso x5 x6 -> rel_iso nat_iso (x3 x5) (x4 x6)) (x5 : Original.LF_DOT_Imp.LF.Imp.state)
    (x6 : imported_String_string -> imported_nat) (hx1 : forall (x7 : String.string) (x8 : imported_String_string), rel_iso String_string_iso x7 x8 -> rel_iso nat_iso (x5 x7) (x6 x8))
    (x7 : Original.LF_DOT_Imp.LF.Imp.BreakImp.result) (x8 : imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_result) (hx2 : rel_iso Original_LF__DOT__Imp_LF_Imp_BreakImp_result_iso x7 x8)
    (x9 : Original.LF_DOT_Imp.LF.Imp.BreakImp.ceval (Original.LF_DOT_Imp.LF.Imp.BreakImp.CSeq Original.LF_DOT_Imp.LF.Imp.BreakImp.CBreak x1) x3 x7 x5)
    (x10 : imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval (imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_CSeq imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_CBreak x2)
             (fun x : imported_String_string => x4 x) x8 (fun x : imported_String_string => x6 x)),
  rel_iso
    (Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval_iso (Original_LF__DOT__Imp_LF_Imp_BreakImp_CSeq_iso Original_LF__DOT__Imp_LF_Imp_BreakImp_CBreak_iso hx) x3 (fun x : imported_String_string => x4 x)
       (fun (x11 : String.string) (x12 : imported_String_string) (hx3 : rel_iso String_string_iso x11 x12) => hx0 x11 x12 hx3) hx2 x5 (fun x : imported_String_string => x6 x)
       (fun (x11 : String.string) (x12 : imported_String_string) (hx3 : rel_iso String_string_iso x11 x12) => hx1 x11 x12 hx3))
    x9 x10 ->
  rel_iso
    (Corelib_Init_Logic_eq_iso
       (IsoFunND x3 (fun x12 : imported_String_string => x4 x12) (fun (x11 : String.string) (x12 : imported_String_string) (hx4 : rel_iso String_string_iso x11 x12) => hx0 x11 x12 hx4))
       (IsoFunND x5 (fun x12 : imported_String_string => x6 x12) (fun (x11 : String.string) (x12 : imported_String_string) (hx4 : rel_iso String_string_iso x11 x12) => hx1 x11 x12 hx4)))
    (Original.LF_DOT_Imp.LF.Imp.BreakImp.break_ignore x1 x3 x5 x7 x9) (imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_break__ignore x4 x6 x10).
Existing Instance Original_LF__DOT__Imp_LF_Imp_BreakImp_break__ignore_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.BreakImp.break_ignore ?x) => unify x Original_LF__DOT__Imp_LF_Imp_BreakImp_break__ignore_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.BreakImp.break_ignore imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_break__ignore ?x) => unify x Original_LF__DOT__Imp_LF_Imp_BreakImp_break__ignore_iso; constructor : typeclass_instances.


End Interface.