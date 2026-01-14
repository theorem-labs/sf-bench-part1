From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.

  Export Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.Args <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Basics_LF_Basics_true : imported_Original_LF__DOT__Basics_LF_Basics_bool.
Parameter Original_LF__DOT__Basics_LF_Basics_true_iso : rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso Original.LF_DOT_Basics.LF.Basics.true imported_Original_LF__DOT__Basics_LF_Basics_true.
Existing Instance Original_LF__DOT__Basics_LF_Basics_true_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.true ?x) => unify x Original_LF__DOT__Basics_LF_Basics_true_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.true imported_Original_LF__DOT__Basics_LF_Basics_true ?x) => unify x Original_LF__DOT__Basics_LF_Basics_true_iso; constructor : typeclass_instances.


End Interface.