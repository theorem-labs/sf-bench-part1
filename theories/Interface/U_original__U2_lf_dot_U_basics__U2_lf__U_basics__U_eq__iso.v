From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__comparison__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__comparison__iso.

  Export Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__comparison__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__comparison__iso.Args <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__comparison__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Basics_LF_Basics_Eq : imported_Original_LF__DOT__Basics_LF_Basics_comparison.
Parameter Original_LF__DOT__Basics_LF_Basics_Eq_iso : rel_iso Original_LF__DOT__Basics_LF_Basics_comparison_iso Original.LF_DOT_Basics.LF.Basics.Eq imported_Original_LF__DOT__Basics_LF_Basics_Eq.
Existing Instance Original_LF__DOT__Basics_LF_Basics_Eq_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.Eq ?x) => unify x Original_LF__DOT__Basics_LF_Basics_Eq_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.Eq imported_Original_LF__DOT__Basics_LF_Basics_Eq ?x) => unify x Original_LF__DOT__Basics_LF_Basics_Eq_iso; constructor : typeclass_instances.


End Interface.