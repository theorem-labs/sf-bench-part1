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

Parameter imported_Original_LF__DOT__Basics_LF_Basics_Lt : imported_Original_LF__DOT__Basics_LF_Basics_comparison.
Parameter Original_LF__DOT__Basics_LF_Basics_Lt_iso : rel_iso Original_LF__DOT__Basics_LF_Basics_comparison_iso Original.LF_DOT_Basics.LF.Basics.Lt imported_Original_LF__DOT__Basics_LF_Basics_Lt.
Existing Instance Original_LF__DOT__Basics_LF_Basics_Lt_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.Lt ?x) => unify x Original_LF__DOT__Basics_LF_Basics_Lt_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.Lt imported_Original_LF__DOT__Basics_LF_Basics_Lt ?x) => unify x Original_LF__DOT__Basics_LF_Basics_Lt_iso; constructor : typeclass_instances.


End Interface.