From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__U_repeat__com__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso Interface.U_string__string__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__U_repeat__com__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso Interface.U_string__string__iso.

  Export Interface.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__U_repeat__com__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso.CodeBlocks Interface.U_string__string__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_auto__U2_lf__U_auto__U_repeat__com__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso.Interface <+ Interface.U_string__string__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Auto_LF_Auto_Repeat_CAsgn : imported_String_string -> imported_Original_LF__DOT__Imp_LF_Imp_aexp -> imported_Original_LF__DOT__Auto_LF_Auto_Repeat_com.
Parameter Original_LF__DOT__Auto_LF_Auto_Repeat_CAsgn_iso : forall (x1 : String.string) (x2 : imported_String_string),
  rel_iso String_string_iso x1 x2 ->
  forall (x3 : Original.LF_DOT_Imp.LF.Imp.aexp) (x4 : imported_Original_LF__DOT__Imp_LF_Imp_aexp),
  rel_iso Original_LF__DOT__Imp_LF_Imp_aexp_iso x3 x4 ->
  rel_iso Original_LF__DOT__Auto_LF_Auto_Repeat_com_iso (Original.LF_DOT_Auto.LF.Auto.Repeat.CAsgn x1 x3) (imported_Original_LF__DOT__Auto_LF_Auto_Repeat_CAsgn x2 x4).
Existing Instance Original_LF__DOT__Auto_LF_Auto_Repeat_CAsgn_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Auto.LF.Auto.Repeat.CAsgn ?x) => unify x Original_LF__DOT__Auto_LF_Auto_Repeat_CAsgn_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Auto.LF.Auto.Repeat.CAsgn imported_Original_LF__DOT__Auto_LF_Auto_Repeat_CAsgn ?x) => unify x Original_LF__DOT__Auto_LF_Auto_Repeat_CAsgn_iso; constructor : typeclass_instances.


End Interface.