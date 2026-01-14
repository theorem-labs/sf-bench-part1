From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_string__string__iso Interface.nat__iso Interface.option__iso Interface.prod__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_string__string__iso Interface.nat__iso Interface.option__iso Interface.prod__iso.

  Export Interface.U_string__string__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.option__iso.CodeBlocks Interface.prod__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_string__string__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.option__iso.Interface <+ Interface.prod__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Imp_LF_Imp_manual__grade__for__XtimesYinZ__spec : imported_option (imported_prod imported_nat imported_String_string).
Parameter Original_LF__DOT__Imp_LF_Imp_manual__grade__for__XtimesYinZ__spec_iso : rel_iso (option_iso (prod_iso nat_iso String_string_iso)) Original.LF_DOT_Imp.LF.Imp.manual_grade_for_XtimesYinZ_spec imported_Original_LF__DOT__Imp_LF_Imp_manual__grade__for__XtimesYinZ__spec.
Existing Instance Original_LF__DOT__Imp_LF_Imp_manual__grade__for__XtimesYinZ__spec_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.manual_grade_for_XtimesYinZ_spec ?x) => unify x Original_LF__DOT__Imp_LF_Imp_manual__grade__for__XtimesYinZ__spec_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.manual_grade_for_XtimesYinZ_spec imported_Original_LF__DOT__Imp_LF_Imp_manual__grade__for__XtimesYinZ__spec ?x) => unify x Original_LF__DOT__Imp_LF_Imp_manual__grade__for__XtimesYinZ__spec_iso; constructor : typeclass_instances.


End Interface.