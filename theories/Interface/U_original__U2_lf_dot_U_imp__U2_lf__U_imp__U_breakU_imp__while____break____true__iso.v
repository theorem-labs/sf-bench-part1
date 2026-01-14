From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__com__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__result__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__U2_sbreak__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__U2_scontinue__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__bexp__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__U2_cwhile__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.ex__iso Interface.false__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__ceval__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__beval__iso Interface.true__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__com__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__result__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__U2_sbreak__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__U2_scontinue__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__bexp__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__U2_cwhile__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.ex__iso Interface.false__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__ceval__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__beval__iso Interface.true__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__com__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__result__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__U2_sbreak__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__U2_scontinue__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__bexp__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__U2_cwhile__iso.CodeBlocks Interface.U_string__string__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.CodeBlocks Interface.U_string__U_emptyU_string__iso.CodeBlocks Interface.U_string__U_string__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.bool__iso.CodeBlocks Interface.U_ascii__U_ascii__iso.CodeBlocks Interface.ex__iso.CodeBlocks Interface.false__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__ceval__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__beval__iso.CodeBlocks Interface.true__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__com__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__result__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__U2_sbreak__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__U2_scontinue__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__bexp__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__U2_cwhile__iso.Interface <+ Interface.U_string__string__iso.Interface <+ Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.Interface <+ Interface.U_string__U_emptyU_string__iso.Interface <+ Interface.U_string__U_string__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.bool__iso.Interface <+ Interface.U_ascii__U_ascii__iso.Interface <+ Interface.ex__iso.Interface <+ Interface.false__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_breakU_imp__ceval__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__beval__iso.Interface <+ Interface.true__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_while__break__true : forall (x : imported_Original_LF__DOT__Imp_LF_Imp_bexp) (x0 : imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_com) (x1 x2 : imported_String_string -> imported_nat),
  imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval (imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_CWhile x x0) (fun H : imported_String_string => x1 H)
    imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_SContinue (fun H : imported_String_string => x2 H) ->
  imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Imp_LF_Imp_beval (fun H : imported_String_string => x2 H) x) imported_true ->
  imported_ex
    (fun H : imported_String_string -> imported_nat =>
     imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval x0 (fun H0 : imported_String_string => H H0) imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_SBreak (fun H0 : imported_String_string => x2 H0)).
Parameter Original_LF__DOT__Imp_LF_Imp_BreakImp_while__break__true_iso : forall (x1 : Original.LF_DOT_Imp.LF.Imp.bexp) (x2 : imported_Original_LF__DOT__Imp_LF_Imp_bexp) (hx : rel_iso Original_LF__DOT__Imp_LF_Imp_bexp_iso x1 x2)
    (x3 : Original.LF_DOT_Imp.LF.Imp.BreakImp.com) (x4 : imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_com) (hx0 : rel_iso Original_LF__DOT__Imp_LF_Imp_BreakImp_com_iso x3 x4)
    (x5 : Original.LF_DOT_Imp.LF.Imp.state) (x6 : imported_String_string -> imported_nat)
    (hx1 : forall (x7 : String.string) (x8 : imported_String_string), rel_iso String_string_iso x7 x8 -> rel_iso nat_iso (x5 x7) (x6 x8)) (x7 : Original.LF_DOT_Imp.LF.Imp.state)
    (x8 : imported_String_string -> imported_nat) (hx2 : forall (x9 : String.string) (x10 : imported_String_string), rel_iso String_string_iso x9 x10 -> rel_iso nat_iso (x7 x9) (x8 x10))
    (x9 : Original.LF_DOT_Imp.LF.Imp.BreakImp.ceval (Original.LF_DOT_Imp.LF.Imp.BreakImp.CWhile x1 x3) x5 Original.LF_DOT_Imp.LF.Imp.BreakImp.SContinue x7)
    (x10 : imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval (imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_CWhile x2 x4) (fun H : imported_String_string => x6 H)
             imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_SContinue (fun H : imported_String_string => x8 H)),
  rel_iso
    {|
      to :=
        Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval_iso (Original_LF__DOT__Imp_LF_Imp_BreakImp_CWhile_iso hx hx0) x5 (fun H : imported_String_string => x6 H)
          (fun (x11 : String.string) (x12 : imported_String_string) (hx3 : rel_iso String_string_iso x11 x12) => hx1 x11 x12 hx3) Original_LF__DOT__Imp_LF_Imp_BreakImp_SContinue_iso x7
          (fun H : imported_String_string => x8 H) (fun (x11 : String.string) (x12 : imported_String_string) (hx3 : rel_iso String_string_iso x11 x12) => hx2 x11 x12 hx3);
      from :=
        from
          (Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval_iso (Original_LF__DOT__Imp_LF_Imp_BreakImp_CWhile_iso hx hx0) x5 (fun H : imported_String_string => x6 H)
             (fun (x11 : String.string) (x12 : imported_String_string) (hx3 : rel_iso String_string_iso x11 x12) => hx1 x11 x12 hx3) Original_LF__DOT__Imp_LF_Imp_BreakImp_SContinue_iso x7
             (fun H : imported_String_string => x8 H) (fun (x11 : String.string) (x12 : imported_String_string) (hx3 : rel_iso String_string_iso x11 x12) => hx2 x11 x12 hx3));
      to_from :=
        fun
          x : imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval (imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_CWhile x2 x4) (fun H : imported_String_string => x6 H)
                imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_SContinue (fun H : imported_String_string => x8 H) =>
        to_from
          (Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval_iso (Original_LF__DOT__Imp_LF_Imp_BreakImp_CWhile_iso hx hx0) x5 (fun H : imported_String_string => x6 H)
             (fun (x11 : String.string) (x12 : imported_String_string) (hx3 : rel_iso String_string_iso x11 x12) => hx1 x11 x12 hx3) Original_LF__DOT__Imp_LF_Imp_BreakImp_SContinue_iso x7
             (fun H : imported_String_string => x8 H) (fun (x11 : String.string) (x12 : imported_String_string) (hx3 : rel_iso String_string_iso x11 x12) => hx2 x11 x12 hx3))
          x;
      from_to :=
        fun x : Original.LF_DOT_Imp.LF.Imp.BreakImp.ceval (Original.LF_DOT_Imp.LF.Imp.BreakImp.CWhile x1 x3) x5 Original.LF_DOT_Imp.LF.Imp.BreakImp.SContinue x7 =>
        seq_p_of_t
          (from_to
             (Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval_iso (Original_LF__DOT__Imp_LF_Imp_BreakImp_CWhile_iso hx hx0) x5 (fun H : imported_String_string => x6 H)
                (fun (x11 : String.string) (x12 : imported_String_string) (hx3 : rel_iso String_string_iso x11 x12) => hx1 x11 x12 hx3) Original_LF__DOT__Imp_LF_Imp_BreakImp_SContinue_iso x7
                (fun H : imported_String_string => x8 H) (fun (x11 : String.string) (x12 : imported_String_string) (hx3 : rel_iso String_string_iso x11 x12) => hx2 x11 x12 hx3))
             x)
    |} x9 x10 ->
  forall (x11 : Original.LF_DOT_Imp.LF.Imp.beval x7 x1 = true)
    (x12 : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Imp_LF_Imp_beval (fun H : imported_String_string => x8 H) x2) imported_true),
  rel_iso
    {|
      to :=
        Corelib_Init_Logic_eq_iso
          (Original_LF__DOT__Imp_LF_Imp_beval_iso x7 (fun H : imported_String_string => x8 H)
             (fun (x13 : String.string) (x14 : imported_String_string) (hx4 : rel_iso String_string_iso x13 x14) => hx2 x13 x14 hx4) hx)
          true_iso;
      from :=
        from
          (Corelib_Init_Logic_eq_iso
             (Original_LF__DOT__Imp_LF_Imp_beval_iso x7 (fun H : imported_String_string => x8 H)
                (fun (x13 : String.string) (x14 : imported_String_string) (hx4 : rel_iso String_string_iso x13 x14) => hx2 x13 x14 hx4) hx)
             true_iso);
      to_from :=
        fun x : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Imp_LF_Imp_beval (fun H : imported_String_string => x8 H) x2) imported_true =>
        to_from
          (Corelib_Init_Logic_eq_iso
             (Original_LF__DOT__Imp_LF_Imp_beval_iso x7 (fun H : imported_String_string => x8 H)
                (fun (x13 : String.string) (x14 : imported_String_string) (hx4 : rel_iso String_string_iso x13 x14) => hx2 x13 x14 hx4) hx)
             true_iso)
          x;
      from_to :=
        fun x : Original.LF_DOT_Imp.LF.Imp.beval x7 x1 = true =>
        seq_p_of_t
          (from_to
             (Corelib_Init_Logic_eq_iso
                (Original_LF__DOT__Imp_LF_Imp_beval_iso x7 (fun H : imported_String_string => x8 H)
                   (fun (x13 : String.string) (x14 : imported_String_string) (hx4 : rel_iso String_string_iso x13 x14) => hx2 x13 x14 hx4) hx)
                true_iso)
             x)
    |} x11 x12 ->
  rel_iso
    {|
      to :=
        ex_iso (fun st'' : Original.LF_DOT_Imp.LF.Imp.state => Original.LF_DOT_Imp.LF.Imp.BreakImp.ceval x3 st'' Original.LF_DOT_Imp.LF.Imp.BreakImp.SBreak x7)
          (fun H : imported_String_string -> imported_nat =>
           imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval x4 (fun H0 : imported_String_string => H H0) imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_SBreak
             (fun H0 : imported_String_string => x8 H0))
          (fun (x13 : Original.LF_DOT_Imp.LF.Imp.state) (x14 : imported_String_string -> imported_nat) (hx5 : rel_iso (IsoArrow String_string_iso nat_iso) x13 x14) =>
           Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval_iso hx0 x13 (fun H : imported_String_string => x14 H)
             (fun (x15 : String.string) (x16 : imported_String_string) (hx6 : rel_iso String_string_iso x15 x16) => IsoUnFunND hx5 hx6) Original_LF__DOT__Imp_LF_Imp_BreakImp_SBreak_iso x7
             (fun H : imported_String_string => x8 H) (fun (x15 : String.string) (x16 : imported_String_string) (hx6 : rel_iso String_string_iso x15 x16) => hx2 x15 x16 hx6));
      from :=
        from
          (ex_iso (fun st'' : Original.LF_DOT_Imp.LF.Imp.state => Original.LF_DOT_Imp.LF.Imp.BreakImp.ceval x3 st'' Original.LF_DOT_Imp.LF.Imp.BreakImp.SBreak x7)
             (fun H : imported_String_string -> imported_nat =>
              imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval x4 (fun H0 : imported_String_string => H H0) imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_SBreak
                (fun H0 : imported_String_string => x8 H0))
             (fun (x13 : Original.LF_DOT_Imp.LF.Imp.state) (x14 : imported_String_string -> imported_nat) (hx5 : rel_iso (IsoArrow String_string_iso nat_iso) x13 x14) =>
              Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval_iso hx0 x13 (fun H : imported_String_string => x14 H)
                (fun (x15 : String.string) (x16 : imported_String_string) (hx6 : rel_iso String_string_iso x15 x16) => IsoUnFunND hx5 hx6) Original_LF__DOT__Imp_LF_Imp_BreakImp_SBreak_iso x7
                (fun H : imported_String_string => x8 H) (fun (x15 : String.string) (x16 : imported_String_string) (hx6 : rel_iso String_string_iso x15 x16) => hx2 x15 x16 hx6)));
      to_from :=
        fun
          x : imported_ex
                (fun H : imported_String_string -> imported_nat =>
                 imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval x4 (fun H0 : imported_String_string => H H0) imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_SBreak
                   (fun H0 : imported_String_string => x8 H0)) =>
        to_from
          (ex_iso (fun st'' : Original.LF_DOT_Imp.LF.Imp.state => Original.LF_DOT_Imp.LF.Imp.BreakImp.ceval x3 st'' Original.LF_DOT_Imp.LF.Imp.BreakImp.SBreak x7)
             (fun H : imported_String_string -> imported_nat =>
              imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval x4 (fun H0 : imported_String_string => H H0) imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_SBreak
                (fun H0 : imported_String_string => x8 H0))
             (fun (x13 : Original.LF_DOT_Imp.LF.Imp.state) (x14 : imported_String_string -> imported_nat) (hx5 : rel_iso (IsoArrow String_string_iso nat_iso) x13 x14) =>
              Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval_iso hx0 x13 (fun H : imported_String_string => x14 H)
                (fun (x15 : String.string) (x16 : imported_String_string) (hx6 : rel_iso String_string_iso x15 x16) => IsoUnFunND hx5 hx6) Original_LF__DOT__Imp_LF_Imp_BreakImp_SBreak_iso x7
                (fun H : imported_String_string => x8 H) (fun (x15 : String.string) (x16 : imported_String_string) (hx6 : rel_iso String_string_iso x15 x16) => hx2 x15 x16 hx6)))
          x;
      from_to :=
        fun x : exists y : Original.LF_DOT_Imp.LF.Imp.state, Original.LF_DOT_Imp.LF.Imp.BreakImp.ceval x3 y Original.LF_DOT_Imp.LF.Imp.BreakImp.SBreak x7 =>
        seq_p_of_t
          (from_to
             (ex_iso (fun st'' : Original.LF_DOT_Imp.LF.Imp.state => Original.LF_DOT_Imp.LF.Imp.BreakImp.ceval x3 st'' Original.LF_DOT_Imp.LF.Imp.BreakImp.SBreak x7)
                (fun H : imported_String_string -> imported_nat =>
                 imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval x4 (fun H0 : imported_String_string => H H0) imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_SBreak
                   (fun H0 : imported_String_string => x8 H0))
                (fun (x13 : Original.LF_DOT_Imp.LF.Imp.state) (x14 : imported_String_string -> imported_nat) (hx5 : rel_iso (IsoArrow String_string_iso nat_iso) x13 x14) =>
                 Original_LF__DOT__Imp_LF_Imp_BreakImp_ceval_iso hx0 x13 (fun H : imported_String_string => x14 H)
                   (fun (x15 : String.string) (x16 : imported_String_string) (hx6 : rel_iso String_string_iso x15 x16) => IsoUnFunND hx5 hx6) Original_LF__DOT__Imp_LF_Imp_BreakImp_SBreak_iso x7
                   (fun H : imported_String_string => x8 H) (fun (x15 : String.string) (x16 : imported_String_string) (hx6 : rel_iso String_string_iso x15 x16) => hx2 x15 x16 hx6)))
             x)
    |} (Original.LF_DOT_Imp.LF.Imp.BreakImp.while_break_true x1 x3 x5 x7 x9 x11) (imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_while__break__true x6 x8 x10 x12).
Existing Instance Original_LF__DOT__Imp_LF_Imp_BreakImp_while__break__true_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.BreakImp.while_break_true ?x) => unify x Original_LF__DOT__Imp_LF_Imp_BreakImp_while__break__true_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.BreakImp.while_break_true imported_Original_LF__DOT__Imp_LF_Imp_BreakImp_while__break__true ?x) => unify x Original_LF__DOT__Imp_LF_Imp_BreakImp_while__break__true_iso; constructor : typeclass_instances.


End Interface.