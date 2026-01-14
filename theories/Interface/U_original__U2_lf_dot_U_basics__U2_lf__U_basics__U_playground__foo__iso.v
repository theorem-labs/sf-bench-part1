From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__rgb__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__rgb__iso.

  Export Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__rgb__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__rgb__iso.Args <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__rgb__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Basics_LF_Basics_Playground_foo : imported_Original_LF__DOT__Basics_LF_Basics_rgb.
Parameter Original_LF__DOT__Basics_LF_Basics_Playground_foo_iso : rel_iso Original_LF__DOT__Basics_LF_Basics_rgb_iso Original.LF_DOT_Basics.LF.Basics.Playground.foo imported_Original_LF__DOT__Basics_LF_Basics_Playground_foo.
Existing Instance Original_LF__DOT__Basics_LF_Basics_Playground_foo_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.Playground.foo ?x) => unify x Original_LF__DOT__Basics_LF_Basics_Playground_foo_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.Playground.foo imported_Original_LF__DOT__Basics_LF_Basics_Playground_foo ?x) => unify x Original_LF__DOT__Basics_LF_Basics_Playground_foo_iso; constructor : typeclass_instances.


End Interface.