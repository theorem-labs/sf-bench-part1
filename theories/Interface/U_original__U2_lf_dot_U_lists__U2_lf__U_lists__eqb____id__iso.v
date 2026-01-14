From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__id__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__id__iso.

  Export Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__id__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.Interface <+ Interface.U_original__U2_lf_dot_U_lists__U2_lf__U_lists__id__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Lists_LF_Lists_eqb__id : imported_Original_LF__DOT__Lists_LF_Lists_id -> imported_Original_LF__DOT__Lists_LF_Lists_id -> imported_Original_LF__DOT__Basics_LF_Basics_bool.
Parameter Original_LF__DOT__Lists_LF_Lists_eqb__id_iso : forall (x1 : Original.LF_DOT_Lists.LF.Lists.id) (x2 : imported_Original_LF__DOT__Lists_LF_Lists_id),
  rel_iso Original_LF__DOT__Lists_LF_Lists_id_iso x1 x2 ->
  forall (x3 : Original.LF_DOT_Lists.LF.Lists.id) (x4 : imported_Original_LF__DOT__Lists_LF_Lists_id),
  rel_iso Original_LF__DOT__Lists_LF_Lists_id_iso x3 x4 ->
  rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso (Original.LF_DOT_Lists.LF.Lists.eqb_id x1 x3) (imported_Original_LF__DOT__Lists_LF_Lists_eqb__id x2 x4).
Existing Instance Original_LF__DOT__Lists_LF_Lists_eqb__id_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Lists.LF.Lists.eqb_id ?x) => unify x Original_LF__DOT__Lists_LF_Lists_eqb__id_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Lists.LF.Lists.eqb_id imported_Original_LF__DOT__Lists_LF_Lists_eqb__id ?x) => unify x Original_LF__DOT__Lists_LF_Lists_eqb__id_iso; constructor : typeclass_instances.


End Interface.