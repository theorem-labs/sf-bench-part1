From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__sinstr__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.false__iso Interface.list__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__s____compile__iso Interface.cons__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aeval__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__s____execute__iso Interface.true__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__sinstr__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.false__iso Interface.list__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__s____compile__iso Interface.cons__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aeval__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__s____execute__iso Interface.true__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__sinstr__iso.CodeBlocks Interface.U_string__string__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.CodeBlocks Interface.U_string__U_emptyU_string__iso.CodeBlocks Interface.U_string__U_string__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.bool__iso.CodeBlocks Interface.U_ascii__U_ascii__iso.CodeBlocks Interface.false__iso.CodeBlocks Interface.list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__s____compile__iso.CodeBlocks Interface.cons__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aeval__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__s____execute__iso.CodeBlocks Interface.true__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__sinstr__iso.Interface <+ Interface.U_string__string__iso.Interface <+ Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.Interface <+ Interface.U_string__U_emptyU_string__iso.Interface <+ Interface.U_string__U_string__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.bool__iso.Interface <+ Interface.U_ascii__U_ascii__iso.Interface <+ Interface.false__iso.Interface <+ Interface.list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__s____compile__iso.Interface <+ Interface.cons__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aeval__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__s____execute__iso.Interface <+ Interface.true__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Imp_LF_Imp_s__compile__correct__aux : forall (x : imported_String_string -> imported_nat) (x0 : imported_Original_LF__DOT__Imp_LF_Imp_aexp) (x1 : imported_list imported_nat),
  imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Imp_LF_Imp_s__execute (fun x2 : imported_String_string => x x2) x1 (imported_Original_LF__DOT__Imp_LF_Imp_s__compile x0))
    (imported_cons (imported_Original_LF__DOT__Imp_LF_Imp_aeval (fun x2 : imported_String_string => x x2) x0) x1).
Parameter Original_LF__DOT__Imp_LF_Imp_s__compile__correct__aux_iso : forall (x1 : Original.LF_DOT_Imp.LF.Imp.state) (x2 : imported_String_string -> imported_nat)
    (hx : forall (x3 : String.string) (x4 : imported_String_string), rel_iso String_string_iso x3 x4 -> rel_iso nat_iso (x1 x3) (x2 x4)) (x3 : Original.LF_DOT_Imp.LF.Imp.aexp)
    (x4 : imported_Original_LF__DOT__Imp_LF_Imp_aexp) (hx0 : rel_iso Original_LF__DOT__Imp_LF_Imp_aexp_iso x3 x4) (x5 : list nat) (x6 : imported_list imported_nat)
    (hx1 : rel_iso (list_iso nat_iso) x5 x6),
  rel_iso
    (Corelib_Init_Logic_eq_iso
       (Original_LF__DOT__Imp_LF_Imp_s__execute_iso x1 (fun x : imported_String_string => x2 x)
          (fun (x7 : String.string) (x8 : imported_String_string) (hx2 : rel_iso String_string_iso x7 x8) => hx x7 x8 hx2) hx1 (Original_LF__DOT__Imp_LF_Imp_s__compile_iso hx0))
       (cons_iso
          (Original_LF__DOT__Imp_LF_Imp_aeval_iso x1 (fun x : imported_String_string => x2 x)
             (fun (x7 : String.string) (x8 : imported_String_string) (hx2 : rel_iso String_string_iso x7 x8) => hx x7 x8 hx2) hx0)
          hx1))
    (Original.LF_DOT_Imp.LF.Imp.s_compile_correct_aux x1 x3 x5) (imported_Original_LF__DOT__Imp_LF_Imp_s__compile__correct__aux x2 x4 x6).
Existing Instance Original_LF__DOT__Imp_LF_Imp_s__compile__correct__aux_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.s_compile_correct_aux ?x) => unify x Original_LF__DOT__Imp_LF_Imp_s__compile__correct__aux_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.s_compile_correct_aux imported_Original_LF__DOT__Imp_LF_Imp_s__compile__correct__aux ?x) => unify x Original_LF__DOT__Imp_LF_Imp_s__compile__correct__aux_iso; constructor : typeclass_instances.


End Interface.