From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__plus2__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_x__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.false__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__ceval__iso Interface.U_peanoU_nat__U_nat__add__iso Interface.U_s__iso Interface.__0__iso Interface.true__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__plus2__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_x__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.false__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__ceval__iso Interface.U_peanoU_nat__U_nat__add__iso Interface.U_s__iso Interface.__0__iso Interface.true__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__plus2__iso.CodeBlocks Interface.U_string__string__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_x__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.CodeBlocks Interface.U_string__U_emptyU_string__iso.CodeBlocks Interface.U_string__U_string__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.bool__iso.CodeBlocks Interface.U_ascii__U_ascii__iso.CodeBlocks Interface.false__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__ceval__iso.CodeBlocks Interface.U_peanoU_nat__U_nat__add__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks Interface.true__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__plus2__iso.Interface <+ Interface.U_string__string__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_x__iso.Interface <+ Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.Interface <+ Interface.U_string__U_emptyU_string__iso.Interface <+ Interface.U_string__U_string__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.bool__iso.Interface <+ Interface.U_ascii__U_ascii__iso.Interface <+ Interface.false__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__ceval__iso.Interface <+ Interface.U_peanoU_nat__U_nat__add__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface <+ Interface.true__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Imp_LF_Imp_plus2__spec : forall (x : imported_String_string -> imported_nat) (x0 : imported_nat) (x1 : imported_String_string -> imported_nat),
  imported_Corelib_Init_Logic_eq (x imported_Original_LF__DOT__Imp_LF_Imp_X) x0 ->
  imported_Original_LF__DOT__Imp_LF_Imp_ceval imported_Original_LF__DOT__Imp_LF_Imp_plus2 (fun x2 : imported_String_string => x x2) (fun x2 : imported_String_string => x1 x2) ->
  imported_Corelib_Init_Logic_eq (x1 imported_Original_LF__DOT__Imp_LF_Imp_X) (imported_PeanoNat_Nat_add x0 (imported_S (imported_S imported_0))).
Parameter Original_LF__DOT__Imp_LF_Imp_plus2__spec_iso : forall (x1 : String.string -> nat) (x2 : imported_String_string -> imported_nat)
    (hx : forall (x3 : String.string) (x4 : imported_String_string), rel_iso String_string_iso x3 x4 -> rel_iso nat_iso (x1 x3) (x2 x4)) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4)
    (x5 : Original.LF_DOT_Imp.LF.Imp.state) (x6 : imported_String_string -> imported_nat)
    (hx1 : forall (x7 : String.string) (x8 : imported_String_string), rel_iso String_string_iso x7 x8 -> rel_iso nat_iso (x5 x7) (x6 x8)) (x7 : x1 Original.LF_DOT_Imp.LF.Imp.X = x3)
    (x8 : imported_Corelib_Init_Logic_eq (x2 imported_Original_LF__DOT__Imp_LF_Imp_X) x4),
  rel_iso (Corelib_Init_Logic_eq_iso (hx Original.LF_DOT_Imp.LF.Imp.X imported_Original_LF__DOT__Imp_LF_Imp_X Original_LF__DOT__Imp_LF_Imp_X_iso) hx0) x7 x8 ->
  forall (x9 : Original.LF_DOT_Imp.LF.Imp.ceval Original.LF_DOT_Imp.LF.Imp.plus2 x1 x5)
    (x10 : imported_Original_LF__DOT__Imp_LF_Imp_ceval imported_Original_LF__DOT__Imp_LF_Imp_plus2 (fun x : imported_String_string => x2 x) (fun x : imported_String_string => x6 x)),
  rel_iso
    (Original_LF__DOT__Imp_LF_Imp_ceval_iso Original_LF__DOT__Imp_LF_Imp_plus2_iso x1 (fun x : imported_String_string => x2 x)
       (fun (x11 : String.string) (x12 : imported_String_string) (hx3 : rel_iso String_string_iso x11 x12) => hx x11 x12 hx3) x5 (fun x : imported_String_string => x6 x)
       (fun (x11 : String.string) (x12 : imported_String_string) (hx3 : rel_iso String_string_iso x11 x12) => hx1 x11 x12 hx3))
    x9 x10 ->
  rel_iso (Corelib_Init_Logic_eq_iso (hx1 Original.LF_DOT_Imp.LF.Imp.X imported_Original_LF__DOT__Imp_LF_Imp_X Original_LF__DOT__Imp_LF_Imp_X_iso) (PeanoNat_Nat_add_iso hx0 (S_iso (S_iso _0_iso))))
    (Original.LF_DOT_Imp.LF.Imp.plus2_spec x1 x3 x5 x7 x9) (imported_Original_LF__DOT__Imp_LF_Imp_plus2__spec x2 x6 x8 x10).
Existing Instance Original_LF__DOT__Imp_LF_Imp_plus2__spec_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.plus2_spec ?x) => unify x Original_LF__DOT__Imp_LF_Imp_plus2__spec_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.plus2_spec imported_Original_LF__DOT__Imp_LF_Imp_plus2__spec ?x) => unify x Original_LF__DOT__Imp_LF_Imp_plus2__spec_iso; constructor : typeclass_instances.


End Interface.