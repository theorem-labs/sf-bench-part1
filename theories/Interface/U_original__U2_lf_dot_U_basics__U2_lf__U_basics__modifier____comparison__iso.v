From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__comparison__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__modifier__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__comparison__iso Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__modifier__iso.

  Export Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__comparison__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__modifier__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__comparison__iso.Interface <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__modifier__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Basics_LF_Basics_modifier__comparison : imported_Original_LF__DOT__Basics_LF_Basics_modifier -> imported_Original_LF__DOT__Basics_LF_Basics_modifier -> imported_Original_LF__DOT__Basics_LF_Basics_comparison.
Parameter Original_LF__DOT__Basics_LF_Basics_modifier__comparison_iso : forall (x1 : Original.LF_DOT_Basics.LF.Basics.modifier) (x2 : imported_Original_LF__DOT__Basics_LF_Basics_modifier),
  rel_iso Original_LF__DOT__Basics_LF_Basics_modifier_iso x1 x2 ->
  forall (x3 : Original.LF_DOT_Basics.LF.Basics.modifier) (x4 : imported_Original_LF__DOT__Basics_LF_Basics_modifier),
  rel_iso Original_LF__DOT__Basics_LF_Basics_modifier_iso x3 x4 ->
  rel_iso Original_LF__DOT__Basics_LF_Basics_comparison_iso (Original.LF_DOT_Basics.LF.Basics.modifier_comparison x1 x3) (imported_Original_LF__DOT__Basics_LF_Basics_modifier__comparison x2 x4).
Existing Instance Original_LF__DOT__Basics_LF_Basics_modifier__comparison_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.modifier_comparison ?x) => unify x Original_LF__DOT__Basics_LF_Basics_modifier__comparison_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.modifier_comparison imported_Original_LF__DOT__Basics_LF_Basics_modifier__comparison ?x) => unify x Original_LF__DOT__Basics_LF_Basics_modifier__comparison_iso; constructor : typeclass_instances.


End Interface.