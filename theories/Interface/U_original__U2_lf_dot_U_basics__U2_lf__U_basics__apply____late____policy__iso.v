From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__grade__iso Interface.nat__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__grade__iso Interface.nat__iso.

  Export Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__grade__iso.CodeBlocks Interface.nat__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__grade__iso.Interface <+ Interface.nat__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Basics_LF_Basics_apply__late__policy : imported_nat -> imported_Original_LF__DOT__Basics_LF_Basics_grade -> imported_Original_LF__DOT__Basics_LF_Basics_grade.
Parameter Original_LF__DOT__Basics_LF_Basics_apply__late__policy_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 ->
  forall (x3 : Original.LF_DOT_Basics.LF.Basics.grade) (x4 : imported_Original_LF__DOT__Basics_LF_Basics_grade),
  rel_iso Original_LF__DOT__Basics_LF_Basics_grade_iso x3 x4 ->
  rel_iso Original_LF__DOT__Basics_LF_Basics_grade_iso (Original.LF_DOT_Basics.LF.Basics.apply_late_policy x1 x3) (imported_Original_LF__DOT__Basics_LF_Basics_apply__late__policy x2 x4).
Existing Instance Original_LF__DOT__Basics_LF_Basics_apply__late__policy_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.apply_late_policy ?x) => unify x Original_LF__DOT__Basics_LF_Basics_apply__late__policy_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.apply_late_policy imported_Original_LF__DOT__Basics_LF_Basics_apply__late__policy ?x) => unify x Original_LF__DOT__Basics_LF_Basics_apply__late__policy_iso; constructor : typeclass_instances.


End Interface.