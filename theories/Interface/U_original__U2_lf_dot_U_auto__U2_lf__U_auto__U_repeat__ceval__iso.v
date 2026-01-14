From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__U_repeat__com__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__U_repeat__com__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.

  Export Interface.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__U_repeat__com__iso.CodeBlocks Interface.U_string__string__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__U_repeat__com__iso.Interface <+ Interface.U_string__string__iso.Interface <+ Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Auto_LF_Auto_Repeat_ceval : imported_Original_LF__DOT__Auto_LF_Auto_Repeat_com -> (imported_String_string -> imported_nat) -> (imported_String_string -> imported_nat) -> SProp.
Parameter Original_LF__DOT__Auto_LF_Auto_Repeat_ceval_iso : forall (x1 : Original.LF_DOT_Auto.LF.Auto.Repeat.com) (x2 : imported_Original_LF__DOT__Auto_LF_Auto_Repeat_com),
  rel_iso Original_LF__DOT__Auto_LF_Auto_Repeat_com_iso x1 x2 ->
  forall (x3 : Original.LF_DOT_Imp.LF.Imp.state) (x4 : imported_String_string -> imported_nat),
  (forall (x5 : String.string) (x6 : imported_String_string), rel_iso String_string_iso x5 x6 -> rel_iso nat_iso (x3 x5) (x4 x6)) ->
  forall (x5 : Original.LF_DOT_Imp.LF.Imp.state) (x6 : imported_String_string -> imported_nat),
  (forall (x7 : String.string) (x8 : imported_String_string), rel_iso String_string_iso x7 x8 -> rel_iso nat_iso (x5 x7) (x6 x8)) ->
  Iso (Original.LF_DOT_Auto.LF.Auto.Repeat.ceval x1 x3 x5) (imported_Original_LF__DOT__Auto_LF_Auto_Repeat_ceval x2 x4 x6).
Existing Instance Original_LF__DOT__Auto_LF_Auto_Repeat_ceval_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Auto.LF.Auto.Repeat.ceval ?x) => unify x Original_LF__DOT__Auto_LF_Auto_Repeat_ceval_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Auto.LF.Auto.Repeat.ceval imported_Original_LF__DOT__Auto_LF_Auto_Repeat_ceval ?x) => unify x Original_LF__DOT__Auto_LF_Auto_Repeat_ceval_iso; constructor : typeclass_instances.


End Interface.