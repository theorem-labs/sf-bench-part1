From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bw__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bw__iso.

  Export Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bw__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bw__iso.Args <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bw__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Basics_LF_Basics_invert : imported_Original_LF__DOT__Basics_LF_Basics_bw -> imported_Original_LF__DOT__Basics_LF_Basics_bw.
Parameter Original_LF__DOT__Basics_LF_Basics_invert_iso : forall (x1 : Original.LF_DOT_Basics.LF.Basics.bw) (x2 : imported_Original_LF__DOT__Basics_LF_Basics_bw),
  rel_iso Original_LF__DOT__Basics_LF_Basics_bw_iso x1 x2 ->
  rel_iso Original_LF__DOT__Basics_LF_Basics_bw_iso (Original.LF_DOT_Basics.LF.Basics.invert x1) (imported_Original_LF__DOT__Basics_LF_Basics_invert x2).
Existing Instance Original_LF__DOT__Basics_LF_Basics_invert_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.invert ?x) => unify x Original_LF__DOT__Basics_LF_Basics_invert_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.invert imported_Original_LF__DOT__Basics_LF_Basics_invert ?x) => unify x Original_LF__DOT__Basics_LF_Basics_invert_iso; constructor : typeclass_instances.


End Interface.