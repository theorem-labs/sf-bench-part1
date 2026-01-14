From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.

  Export Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso.CodeBlocks Interface.U_string__string__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso.Interface <+ Interface.U_string__string__iso.Interface <+ Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Imp_LF_Imp_aeval : (imported_String_string -> imported_nat) -> imported_Original_LF__DOT__Imp_LF_Imp_aexp -> imported_nat.
Parameter Original_LF__DOT__Imp_LF_Imp_aeval_iso : forall (x1 : Original.LF_DOT_Imp.LF.Imp.state) (x2 : imported_String_string -> imported_nat),
  (forall (x3 : String.string) (x4 : imported_String_string), rel_iso String_string_iso x3 x4 -> rel_iso nat_iso (x1 x3) (x2 x4)) ->
  forall (x3 : Original.LF_DOT_Imp.LF.Imp.aexp) (x4 : imported_Original_LF__DOT__Imp_LF_Imp_aexp),
  rel_iso Original_LF__DOT__Imp_LF_Imp_aexp_iso x3 x4 -> rel_iso nat_iso (Original.LF_DOT_Imp.LF.Imp.aeval x1 x3) (imported_Original_LF__DOT__Imp_LF_Imp_aeval x2 x4).
Existing Instance Original_LF__DOT__Imp_LF_Imp_aeval_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.aeval ?x) => unify x Original_LF__DOT__Imp_LF_Imp_aeval_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.aeval imported_Original_LF__DOT__Imp_LF_Imp_aeval ?x) => unify x Original_LF__DOT__Imp_LF_Imp_aeval_iso; constructor : typeclass_instances.


End Interface.