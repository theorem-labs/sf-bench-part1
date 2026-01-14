From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__day__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__day__iso.

  Export Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__day__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__day__iso.Args <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__day__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Basics_LF_Basics_next__working__day : imported_Original_LF__DOT__Basics_LF_Basics_day -> imported_Original_LF__DOT__Basics_LF_Basics_day.
Parameter Original_LF__DOT__Basics_LF_Basics_next__working__day_iso : forall (x1 : Original.LF_DOT_Basics.LF.Basics.day) (x2 : imported_Original_LF__DOT__Basics_LF_Basics_day),
  rel_iso Original_LF__DOT__Basics_LF_Basics_day_iso x1 x2 ->
  rel_iso Original_LF__DOT__Basics_LF_Basics_day_iso (Original.LF_DOT_Basics.LF.Basics.next_working_day x1) (imported_Original_LF__DOT__Basics_LF_Basics_next__working__day x2).
Existing Instance Original_LF__DOT__Basics_LF_Basics_next__working__day_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.next_working_day ?x) => unify x Original_LF__DOT__Basics_LF_Basics_next__working__day_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.next_working_day imported_Original_LF__DOT__Basics_LF_Basics_next__working__day ?x) => unify x Original_LF__DOT__Basics_LF_Basics_next__working__day_iso; constructor : typeclass_instances.


End Interface.