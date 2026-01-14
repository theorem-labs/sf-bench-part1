From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.U_false__iso Interface.U_logic__not__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__loop__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.false__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__ceval__iso Interface.true__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.U_false__iso Interface.U_logic__not__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__loop__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.false__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__ceval__iso Interface.true__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.U_false__iso.CodeBlocks Interface.U_logic__not__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__loop__iso.CodeBlocks Interface.U_string__string__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.CodeBlocks Interface.U_string__U_emptyU_string__iso.CodeBlocks Interface.U_string__U_string__iso.CodeBlocks Interface.bool__iso.CodeBlocks Interface.U_ascii__U_ascii__iso.CodeBlocks Interface.false__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__ceval__iso.CodeBlocks Interface.true__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.U_false__iso.Interface <+ Interface.U_logic__not__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__loop__iso.Interface <+ Interface.U_string__string__iso.Interface <+ Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.Interface <+ Interface.U_string__U_emptyU_string__iso.Interface <+ Interface.U_string__U_string__iso.Interface <+ Interface.bool__iso.Interface <+ Interface.U_ascii__U_ascii__iso.Interface <+ Interface.false__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__ceval__iso.Interface <+ Interface.true__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Imp_LF_Imp_loop__never__stops : forall x x0 : imported_String_string -> imported_nat,
  imported_Original_LF__DOT__Imp_LF_Imp_ceval imported_Original_LF__DOT__Imp_LF_Imp_loop (fun x1 : imported_String_string => x x1) (fun x1 : imported_String_string => x0 x1) -> imported_False.
Parameter Original_LF__DOT__Imp_LF_Imp_loop__never__stops_iso : forall (x1 : Original.LF_DOT_Imp.LF.Imp.state) (x2 : imported_String_string -> imported_nat)
    (hx : forall (x3 : String.string) (x4 : imported_String_string), rel_iso String_string_iso x3 x4 -> rel_iso nat_iso (x1 x3) (x2 x4)) (x3 : Original.LF_DOT_Imp.LF.Imp.state)
    (x4 : imported_String_string -> imported_nat) (hx0 : forall (x5 : String.string) (x6 : imported_String_string), rel_iso String_string_iso x5 x6 -> rel_iso nat_iso (x3 x5) (x4 x6))
    (x5 : Original.LF_DOT_Imp.LF.Imp.ceval Original.LF_DOT_Imp.LF.Imp.loop x1 x3)
    (x6 : imported_Original_LF__DOT__Imp_LF_Imp_ceval imported_Original_LF__DOT__Imp_LF_Imp_loop (fun x : imported_String_string => x2 x) (fun x : imported_String_string => x4 x)),
  rel_iso
    (Original_LF__DOT__Imp_LF_Imp_ceval_iso Original_LF__DOT__Imp_LF_Imp_loop_iso x1 (fun x : imported_String_string => x2 x)
       (fun (x7 : String.string) (x8 : imported_String_string) (hx1 : rel_iso String_string_iso x7 x8) => hx x7 x8 hx1) x3 (fun x : imported_String_string => x4 x)
       (fun (x7 : String.string) (x8 : imported_String_string) (hx1 : rel_iso String_string_iso x7 x8) => hx0 x7 x8 hx1))
    x5 x6 ->
  rel_iso False_iso (Original.LF_DOT_Imp.LF.Imp.loop_never_stops x1 x3 x5) (imported_Original_LF__DOT__Imp_LF_Imp_loop__never__stops x2 x4 x6).
Existing Instance Original_LF__DOT__Imp_LF_Imp_loop__never__stops_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.loop_never_stops ?x) => unify x Original_LF__DOT__Imp_LF_Imp_loop__never__stops_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.loop_never_stops imported_Original_LF__DOT__Imp_LF_Imp_loop__never__stops ?x) => unify x Original_LF__DOT__Imp_LF_Imp_loop__never__stops_iso; constructor : typeclass_instances.


End Interface.