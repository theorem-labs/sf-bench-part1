From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.false__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso Interface.le__iso Interface.option__iso Interface.U_original__U2_lf_dot_U_impU2_cevalU_fun__U2_lf__U_impU2_cevalU_fun__ceval____step__iso Interface.U_some__iso Interface.true__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.false__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso Interface.le__iso Interface.option__iso Interface.U_original__U2_lf_dot_U_impU2_cevalU_fun__U2_lf__U_impU2_cevalU_fun__ceval____step__iso Interface.U_some__iso Interface.true__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso.CodeBlocks Interface.U_string__string__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.CodeBlocks Interface.U_string__U_emptyU_string__iso.CodeBlocks Interface.U_string__U_string__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.bool__iso.CodeBlocks Interface.U_ascii__U_ascii__iso.CodeBlocks Interface.false__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.CodeBlocks Interface.le__iso.CodeBlocks Interface.option__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_impU2_cevalU_fun__U2_lf__U_impU2_cevalU_fun__ceval____step__iso.CodeBlocks Interface.U_some__iso.CodeBlocks Interface.true__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso.Interface <+ Interface.U_string__string__iso.Interface <+ Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.Interface <+ Interface.U_string__U_emptyU_string__iso.Interface <+ Interface.U_string__U_string__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.bool__iso.Interface <+ Interface.U_ascii__U_ascii__iso.Interface <+ Interface.false__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.Interface <+ Interface.le__iso.Interface <+ Interface.option__iso.Interface <+ Interface.U_original__U2_lf_dot_U_impU2_cevalU_fun__U2_lf__U_impU2_cevalU_fun__ceval____step__iso.Interface <+ Interface.U_some__iso.Interface <+ Interface.true__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step__more : forall (x x0 : imported_nat) (x1 x2 : imported_String_string -> imported_nat) (x3 : imported_Original_LF__DOT__Imp_LF_Imp_com),
  imported_le x x0 ->
  imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step (fun x4 : imported_String_string => x1 x4) x3 x)
    (imported_Some (fun x16 : imported_String_string => x2 x16)) ->
  imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step (fun x4 : imported_String_string => x1 x4) x3 x0)
    (imported_Some (fun x16 : imported_String_string => x2 x16)).
Parameter Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step__more_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) (x5 : Original.LF_DOT_Imp.LF.Imp.state)
    (x6 : imported_String_string -> imported_nat) (hx1 : forall (x7 : String.string) (x8 : imported_String_string), rel_iso String_string_iso x7 x8 -> rel_iso nat_iso (x5 x7) (x6 x8))
    (x7 : Original.LF_DOT_Imp.LF.Imp.state) (x8 : imported_String_string -> imported_nat)
    (hx2 : forall (x9 : String.string) (x10 : imported_String_string), rel_iso String_string_iso x9 x10 -> rel_iso nat_iso (x7 x9) (x8 x10)) (x9 : Original.LF_DOT_Imp.LF.Imp.com)
    (x10 : imported_Original_LF__DOT__Imp_LF_Imp_com) (hx3 : rel_iso Original_LF__DOT__Imp_LF_Imp_com_iso x9 x10) (x11 : x1 <= x3) (x12 : imported_le x2 x4),
  rel_iso (le_iso hx hx0) x11 x12 ->
  forall (x13 : Original.LF_DOT_ImpCEvalFun.LF.ImpCEvalFun.ceval_step x5 x9 x1 = Some x7)
    (x14 : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step (fun x : imported_String_string => x6 x) x10 x2)
             (imported_Some (fun x16 : imported_String_string => x8 x16))),
  rel_iso
    (Corelib_Init_Logic_eq_iso
       (Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step_iso x5 (fun x : imported_String_string => x6 x)
          (fun (x15 : String.string) (x16 : imported_String_string) (hx5 : rel_iso String_string_iso x15 x16) => hx1 x15 x16 hx5) hx3 hx)
       (Some_iso (IsoFunND x7 (fun x16 : imported_String_string => x8 x16) (fun (x15 : String.string) (x16 : imported_String_string) (hx5 : rel_iso String_string_iso x15 x16) => hx2 x15 x16 hx5))))
    x13 x14 ->
  rel_iso
    (Corelib_Init_Logic_eq_iso
       (Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step_iso x5 (fun x : imported_String_string => x6 x)
          (fun (x15 : String.string) (x16 : imported_String_string) (hx6 : rel_iso String_string_iso x15 x16) => hx1 x15 x16 hx6) hx3 hx0)
       (Some_iso (IsoFunND x7 (fun x16 : imported_String_string => x8 x16) (fun (x15 : String.string) (x16 : imported_String_string) (hx6 : rel_iso String_string_iso x15 x16) => hx2 x15 x16 hx6))))
    (Original.LF_DOT_ImpCEvalFun.LF.ImpCEvalFun.ceval_step_more x1 x3 x5 x7 x9 x11 x13) (imported_Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step__more x6 x8 x12 x14).
Existing Instance Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step__more_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_ImpCEvalFun.LF.ImpCEvalFun.ceval_step_more ?x) => unify x Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step__more_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_ImpCEvalFun.LF.ImpCEvalFun.ceval_step_more imported_Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step__more ?x) => unify x Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_ceval__step__more_iso; constructor : typeclass_instances.


End Interface.