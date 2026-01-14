From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__com__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__U2_cseq__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__result__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__U2_scontinue__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.false__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__ceval__iso Interface.true__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__com__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__U2_cseq__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__result__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__U2_scontinue__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.false__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__ceval__iso Interface.true__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__com__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__U2_cseq__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__result__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__U2_scontinue__iso.CodeBlocks Interface.U_string__string__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.CodeBlocks Interface.U_string__U_emptyU_string__iso.CodeBlocks Interface.U_string__U_string__iso.CodeBlocks Interface.bool__iso.CodeBlocks Interface.U_ascii__U_ascii__iso.CodeBlocks Interface.false__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__ceval__iso.CodeBlocks Interface.true__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__com__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__U2_cseq__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__result__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__U2_scontinue__iso.Interface <+ Interface.U_string__string__iso.Interface <+ Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.Interface <+ Interface.U_string__U_emptyU_string__iso.Interface <+ Interface.U_string__U_string__iso.Interface <+ Interface.bool__iso.Interface <+ Interface.U_ascii__U_ascii__iso.Interface <+ Interface.false__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__ceval__iso.Interface <+ Interface.true__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_seq__continue : forall (x x0 : imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_com) (x1 x2 x3 : imported_String_string -> imported_nat),
  imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval x (fun x4 : imported_String_string => x1 x4) imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_SContinue (fun x4 : imported_String_string => x2 x4) ->
  imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval x0 (fun x4 : imported_String_string => x2 x4) imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_SContinue
    (fun x4 : imported_String_string => x3 x4) ->
  imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval (imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_CSeq x x0) (fun x4 : imported_String_string => x1 x4)
    imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_SContinue (fun x4 : imported_String_string => x3 x4).
Parameter Original_LF__DOT__Imp_LF_Imp_BreakImp_seq__continue_iso : forall (x1 : Original.LF_DOT_Imp.LF.Imp.BreakImp.com) (x2 : imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_com) (hx : rel_iso Original_LF__DOT__Imp_LF_Imp_BreakImp_com_iso x1 x2)
    (x3 : Original.LF_DOT_Imp.LF.Imp.BreakImp.com) (x4 : imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_com) (hx0 : rel_iso Original_LF__DOT__Imp_LF_Imp_BreakImp_com_iso x3 x4)
    (x5 : Original.LF_DOT_Imp.LF.Imp.state) (x6 : imported_String_string -> imported_nat)
    (hx1 : forall (x7 : String.string) (x8 : imported_String_string), rel_iso String_string_iso x7 x8 -> rel_iso nat_iso (x5 x7) (x6 x8)) (x7 : Original.LF_DOT_Imp.LF.Imp.state)
    (x8 : imported_String_string -> imported_nat) (hx2 : forall (x9 : String.string) (x10 : imported_String_string), rel_iso String_string_iso x9 x10 -> rel_iso nat_iso (x7 x9) (x8 x10))
    (x9 : Original.LF_DOT_Imp.LF.Imp.state) (x10 : imported_String_string -> imported_nat)
    (hx3 : forall (x11 : String.string) (x12 : imported_String_string), rel_iso String_string_iso x11 x12 -> rel_iso nat_iso (x9 x11) (x10 x12))
    (x11 : Original.LF_DOT_Imp.LF.Imp.BreakImp.ceval x1 x5 Original.LF_DOT_Imp.LF.Imp.BreakImp.SContinue x7)
    (x12 : imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval x2 (fun x : imported_String_string => x6 x) imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_SContinue
             (fun x : imported_String_string => x8 x)),
  rel_iso
    (Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval_iso hx x5 (fun x : imported_String_string => x6 x)
       (fun (x13 : String.string) (x14 : imported_String_string) (hx4 : rel_iso String_string_iso x13 x14) => hx1 x13 x14 hx4) Original_LF__DOT__Imp_LF_Imp_BreakImp_SContinue_iso x7
       (fun x : imported_String_string => x8 x) (fun (x13 : String.string) (x14 : imported_String_string) (hx4 : rel_iso String_string_iso x13 x14) => hx2 x13 x14 hx4))
    x11 x12 ->
  forall (x13 : Original.LF_DOT_Imp.LF.Imp.BreakImp.ceval x3 x7 Original.LF_DOT_Imp.LF.Imp.BreakImp.SContinue x9)
    (x14 : imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval x4 (fun x : imported_String_string => x8 x) imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_SContinue
             (fun x : imported_String_string => x10 x)),
  rel_iso
    (Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval_iso hx0 x7 (fun x : imported_String_string => x8 x)
       (fun (x15 : String.string) (x16 : imported_String_string) (hx5 : rel_iso String_string_iso x15 x16) => hx2 x15 x16 hx5) Original_LF__DOT__Imp_LF_Imp_BreakImp_SContinue_iso x9
       (fun x : imported_String_string => x10 x) (fun (x15 : String.string) (x16 : imported_String_string) (hx5 : rel_iso String_string_iso x15 x16) => hx3 x15 x16 hx5))
    x13 x14 ->
  rel_iso
    (Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval_iso (Original_LF__DOT__Imp_LF_Imp_BreakImp_CSeq_iso hx hx0) x5 (fun x : imported_String_string => x6 x)
       (fun (x15 : String.string) (x16 : imported_String_string) (hx6 : rel_iso String_string_iso x15 x16) => hx1 x15 x16 hx6) Original_LF__DOT__Imp_LF_Imp_BreakImp_SContinue_iso x9
       (fun x : imported_String_string => x10 x) (fun (x15 : String.string) (x16 : imported_String_string) (hx6 : rel_iso String_string_iso x15 x16) => hx3 x15 x16 hx6))
    (Original.LF_DOT_Imp.LF.Imp.BreakImp.seq_continue x1 x3 x5 x7 x9 x11 x13) (imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_seq__continue x6 x8 x10 x12 x14).
Existing Instance Original_LF__DOT__Imp_LF_Imp_BreakImp_seq__continue_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.BreakImp.seq_continue ?x) => unify x Original_LF__DOT__Imp_LF_Imp_BreakImp_seq__continue_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.BreakImp.seq_continue imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_seq__continue ?x) => unify x Original_LF__DOT__Imp_LF_Imp_BreakImp_seq__continue_iso; constructor : typeclass_instances.


End Interface.