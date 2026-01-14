From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bin__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bin__iso.

  Export Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bin__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bin__iso.Args <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bin__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Basics_LF_Basics_incr : imported_Original_LF__DOT__Basics_LF_Basics_bin -> imported_Original_LF__DOT__Basics_LF_Basics_bin.
Parameter Original_LF__DOT__Basics_LF_Basics_incr_iso : forall (x1 : Original.LF_DOT_Basics.LF.Basics.bin) (x2 : imported_Original_LF__DOT__Basics_LF_Basics_bin),
  rel_iso Original_LF__DOT__Basics_LF_Basics_bin_iso x1 x2 ->
  rel_iso Original_LF__DOT__Basics_LF_Basics_bin_iso (Original.LF_DOT_Basics.LF.Basics.incr x1) (imported_Original_LF__DOT__Basics_LF_Basics_incr x2).
Existing Instance Original_LF__DOT__Basics_LF_Basics_incr_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.incr ?x) => unify x Original_LF__DOT__Basics_LF_Basics_incr_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.incr imported_Original_LF__DOT__Basics_LF_Basics_incr ?x) => unify x Original_LF__DOT__Basics_LF_Basics_incr_iso; constructor : typeclass_instances.


End Interface.