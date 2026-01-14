From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__grade__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__grade__iso.

  Export Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__grade__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__grade__iso.Args <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__grade__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Basics_LF_Basics_lower__grade : imported_Original_LF__DOT__Basics_LF_Basics_grade -> imported_Original_LF__DOT__Basics_LF_Basics_grade.
Parameter Original_LF__DOT__Basics_LF_Basics_lower__grade_iso : forall (x1 : Original.LF_DOT_Basics.LF.Basics.grade) (x2 : imported_Original_LF__DOT__Basics_LF_Basics_grade),
  rel_iso Original_LF__DOT__Basics_LF_Basics_grade_iso x1 x2 ->
  rel_iso Original_LF__DOT__Basics_LF_Basics_grade_iso (Original.LF_DOT_Basics.LF.Basics.lower_grade x1) (imported_Original_LF__DOT__Basics_LF_Basics_lower__grade x2).
Existing Instance Original_LF__DOT__Basics_LF_Basics_lower__grade_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.lower_grade ?x) => unify x Original_LF__DOT__Basics_LF_Basics_lower__grade_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.lower_grade imported_Original_LF__DOT__Basics_LF_Basics_lower__grade ?x) => unify x Original_LF__DOT__Basics_LF_Basics_lower__grade_iso; constructor : typeclass_instances.


End Interface.