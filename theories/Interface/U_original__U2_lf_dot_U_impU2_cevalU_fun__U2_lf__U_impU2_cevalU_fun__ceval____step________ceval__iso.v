From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.ex__iso Interface.false__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__ceval__iso Interface.option__iso Interface.U_original__U2_lf_dot_U_impU2_cevalU_fun__U2_lf__U_impU2_cevalU_fun__ceval____step__iso Interface.U_some__iso Interface.true__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.ex__iso Interface.false__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__ceval__iso Interface.option__iso Interface.U_original__U2_lf_dot_U_impU2_cevalU_fun__U2_lf__U_impU2_cevalU_fun__ceval____step__iso Interface.U_some__iso Interface.true__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso.CodeBlocks Interface.U_string__string__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.CodeBlocks Interface.U_string__U_emptyU_string__iso.CodeBlocks Interface.U_string__U_string__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.bool__iso.CodeBlocks Interface.U_ascii__U_ascii__iso.CodeBlocks Interface.ex__iso.CodeBlocks Interface.false__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__ceval__iso.CodeBlocks Interface.option__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_impU2_cevalU_fun__U2_lf__U_impU2_cevalU_fun__ceval____step__iso.CodeBlocks Interface.U_some__iso.CodeBlocks Interface.true__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso.Interface <+ Interface.U_string__string__iso.Interface <+ Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.Interface <+ Interface.U_string__U_emptyU_string__iso.Interface <+ Interface.U_string__U_string__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.bool__iso.Interface <+ Interface.U_ascii__U_ascii__iso.Interface <+ Interface.ex__iso.Interface <+ Interface.false__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__ceval__iso.Interface <+ Interface.option__iso.Interface <+ Interface.U_original__U2_lf_dot_U_impU2_cevalU_fun__U2_lf__U_impU2_cevalU_fun__ceval____step__iso.Interface <+ Interface.U_some__iso.Interface <+ Interface.true__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step____ceval : forall (x : imported_Original_LF__DOT__Imp_LF_Imp_com) (x0 x1 : imported_String_string -> imported_nat),
  imported_ex
    (fun H : imported_nat =>
     imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step (fun H0 : imported_String_string => x0 H0) x H)
       (imported_Some (fun x12 : imported_String_string => x1 x12))) ->
  imported_Original_LF__DOT__Imp_LF_Imp_ceval x (fun H : imported_String_string => x0 H) (fun H : imported_String_string => x1 H).
Parameter Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step____ceval_iso : forall (x1 : Original.LF_DOT_Imp.LF.Imp.com) (x2 : imported_Original_LF__DOT__Imp_LF_Imp_com) (hx : rel_iso Original_LF__DOT__Imp_LF_Imp_com_iso x1 x2) (x3 : Original.LF_DOT_Imp.LF.Imp.state)
    (x4 : imported_String_string -> imported_nat) (hx0 : forall (x5 : String.string) (x6 : imported_String_string), rel_iso String_string_iso x5 x6 -> rel_iso nat_iso (x3 x5) (x4 x6))
    (x5 : Original.LF_DOT_Imp.LF.Imp.state) (x6 : imported_String_string -> imported_nat)
    (hx1 : forall (x7 : String.string) (x8 : imported_String_string), rel_iso String_string_iso x7 x8 -> rel_iso nat_iso (x5 x7) (x6 x8))
    (x7 : exists i : nat, Original.LF_DOT_ImpCEvalFun.LF.ImpCEvalFun.ceval_step x3 x1 i = Some x5)
    (x8 : imported_ex
            (fun H : imported_nat =>
             imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step (fun H0 : imported_String_string => x4 H0) x2 H)
               (imported_Some (fun x12 : imported_String_string => x6 x12)))),
  rel_iso
    {|
      to :=
        ex_iso (fun i : nat => Original.LF_DOT_ImpCEvalFun.LF.ImpCEvalFun.ceval_step x3 x1 i = Some x5)
          (fun H : imported_nat =>
           imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step (fun H0 : imported_String_string => x4 H0) x2 H)
             (imported_Some (fun x12 : imported_String_string => x6 x12)))
          (fun (x9 : nat) (x10 : imported_nat) (hx2 : rel_iso nat_iso x9 x10) =>
           Corelib_Init_Logic_eq_iso
             (Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step_iso x3 (fun H : imported_String_string => x4 H)
                (fun (x11 : String.string) (x12 : imported_String_string) (hx3 : rel_iso String_string_iso x11 x12) => hx0 x11 x12 hx3) hx hx2)
             (Some_iso
                (IsoFunND x5 (fun x12 : imported_String_string => x6 x12) (fun (x11 : String.string) (x12 : imported_String_string) (hx3 : rel_iso String_string_iso x11 x12) => hx1 x11 x12 hx3))));
      from :=
        from
          (ex_iso (fun i : nat => Original.LF_DOT_ImpCEvalFun.LF.ImpCEvalFun.ceval_step x3 x1 i = Some x5)
             (fun H : imported_nat =>
              imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step (fun H0 : imported_String_string => x4 H0) x2 H)
                (imported_Some (fun x12 : imported_String_string => x6 x12)))
             (fun (x9 : nat) (x10 : imported_nat) (hx2 : rel_iso nat_iso x9 x10) =>
              Corelib_Init_Logic_eq_iso
                (Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step_iso x3 (fun H : imported_String_string => x4 H)
                   (fun (x11 : String.string) (x12 : imported_String_string) (hx3 : rel_iso String_string_iso x11 x12) => hx0 x11 x12 hx3) hx hx2)
                (Some_iso
                   (IsoFunND x5 (fun x12 : imported_String_string => x6 x12) (fun (x11 : String.string) (x12 : imported_String_string) (hx3 : rel_iso String_string_iso x11 x12) => hx1 x11 x12 hx3)))));
      to_from :=
        fun
          x : imported_ex
                (fun H : imported_nat =>
                 imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step (fun H0 : imported_String_string => x4 H0) x2 H)
                   (imported_Some (fun x12 : imported_String_string => x6 x12))) =>
        to_from
          (ex_iso (fun i : nat => Original.LF_DOT_ImpCEvalFun.LF.ImpCEvalFun.ceval_step x3 x1 i = Some x5)
             (fun H : imported_nat =>
              imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step (fun H0 : imported_String_string => x4 H0) x2 H)
                (imported_Some (fun x12 : imported_String_string => x6 x12)))
             (fun (x9 : nat) (x10 : imported_nat) (hx2 : rel_iso nat_iso x9 x10) =>
              Corelib_Init_Logic_eq_iso
                (Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step_iso x3 (fun H : imported_String_string => x4 H)
                   (fun (x11 : String.string) (x12 : imported_String_string) (hx3 : rel_iso String_string_iso x11 x12) => hx0 x11 x12 hx3) hx hx2)
                (Some_iso
                   (IsoFunND x5 (fun x12 : imported_String_string => x6 x12) (fun (x11 : String.string) (x12 : imported_String_string) (hx3 : rel_iso String_string_iso x11 x12) => hx1 x11 x12 hx3)))))
          x;
      from_to :=
        fun x : exists y : nat, Original.LF_DOT_ImpCEvalFun.LF.ImpCEvalFun.ceval_step x3 x1 y = Some x5 =>
        seq_p_of_t
          (from_to
             (ex_iso (fun i : nat => Original.LF_DOT_ImpCEvalFun.LF.ImpCEvalFun.ceval_step x3 x1 i = Some x5)
                (fun H : imported_nat =>
                 imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step (fun H0 : imported_String_string => x4 H0) x2 H)
                   (imported_Some (fun x12 : imported_String_string => x6 x12)))
                (fun (x9 : nat) (x10 : imported_nat) (hx2 : rel_iso nat_iso x9 x10) =>
                 Corelib_Init_Logic_eq_iso
                   (Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step_iso x3 (fun H : imported_String_string => x4 H)
                      (fun (x11 : String.string) (x12 : imported_String_string) (hx3 : rel_iso String_string_iso x11 x12) => hx0 x11 x12 hx3) hx hx2)
                   (Some_iso
                      (IsoFunND x5 (fun x12 : imported_String_string => x6 x12) (fun (x11 : String.string) (x12 : imported_String_string) (hx3 : rel_iso String_string_iso x11 x12) => hx1 x11 x12 hx3)))))
             x)
    |} x7 x8 ->
  rel_iso
    {|
      to :=
        Original_LF__DOT__Imp_LF_Imp_ceval_iso hx x3 (fun H : imported_String_string => x4 H)
          (fun (x9 : String.string) (x10 : imported_String_string) (hx3 : rel_iso String_string_iso x9 x10) => hx0 x9 x10 hx3) x5 (fun H : imported_String_string => x6 H)
          (fun (x9 : String.string) (x10 : imported_String_string) (hx3 : rel_iso String_string_iso x9 x10) => hx1 x9 x10 hx3);
      from :=
        from
          (Original_LF__DOT__Imp_LF_Imp_ceval_iso hx x3 (fun H : imported_String_string => x4 H)
             (fun (x9 : String.string) (x10 : imported_String_string) (hx3 : rel_iso String_string_iso x9 x10) => hx0 x9 x10 hx3) x5 (fun H : imported_String_string => x6 H)
             (fun (x9 : String.string) (x10 : imported_String_string) (hx3 : rel_iso String_string_iso x9 x10) => hx1 x9 x10 hx3));
      to_from :=
        fun x : imported_Original_LF__DOT__Imp_LF_Imp_ceval x2 (fun H : imported_String_string => x4 H) (fun H : imported_String_string => x6 H) =>
        to_from
          (Original_LF__DOT__Imp_LF_Imp_ceval_iso hx x3 (fun H : imported_String_string => x4 H)
             (fun (x9 : String.string) (x10 : imported_String_string) (hx3 : rel_iso String_string_iso x9 x10) => hx0 x9 x10 hx3) x5 (fun H : imported_String_string => x6 H)
             (fun (x9 : String.string) (x10 : imported_String_string) (hx3 : rel_iso String_string_iso x9 x10) => hx1 x9 x10 hx3))
          x;
      from_to :=
        fun x : Original.LF_DOT_Imp.LF.Imp.ceval x1 x3 x5 =>
        seq_p_of_t
          (from_to
             (Original_LF__DOT__Imp_LF_Imp_ceval_iso hx x3 (fun H : imported_String_string => x4 H)
                (fun (x9 : String.string) (x10 : imported_String_string) (hx3 : rel_iso String_string_iso x9 x10) => hx0 x9 x10 hx3) x5 (fun H : imported_String_string => x6 H)
                (fun (x9 : String.string) (x10 : imported_String_string) (hx3 : rel_iso String_string_iso x9 x10) => hx1 x9 x10 hx3))
             x)
    |} (Original.LF_DOT_ImpCEvalFun.LF.ImpCEvalFun.ceval_step__ceval x1 x3 x5 x7) (imported_Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step____ceval x4 x6 x8).
Existing Instance Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step____ceval_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_ImpCEvalFun.LF.ImpCEvalFun.ceval_step__ceval ?x) => unify x Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step____ceval_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_ImpCEvalFun.LF.ImpCEvalFun.ceval_step__ceval imported_Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step____ceval ?x) => unify x Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step____ceval_iso; constructor : typeclass_instances.


End Interface.