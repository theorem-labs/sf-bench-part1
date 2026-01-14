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

Parameter imported_Original_LF__DOT__Basics_LF_Basics_andb' : imported_Original_LF__DOT__Basics_LF_Basics_bool -> imported_Original_LF__DOT__Basics_LF_Basics_bool -> imported_Original_LF__DOT__Basics_LF_Basics_bool.
Parameter Original_LF__DOT__Basics_LF_Basics_andb'_iso : forall (x1 : Original.LF_DOT_Basics.LF.Basics.bool) (x2 : imported_Original_LF__DOT__Basics_LF_Basics_bool),
  rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso x1 x2 ->
  forall (x3 : Original.LF_DOT_Basics.LF.Basics.bool) (x4 : imported_Original_LF__DOT__Basics_LF_Basics_bool),
  rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso x3 x4 ->
  rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso (Original.LF_DOT_Basics.LF.Basics.andb' x1 x3) (imported_Original_LF__DOT__Basics_LF_Basics_andb' x2 x4).
Existing Instance Original_LF__DOT__Basics_LF_Basics_andb'_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.andb' ?x) => unify x Original_LF__DOT__Basics_LF_Basics_andb'_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.andb' imported_Original_LF__DOT__Basics_LF_Basics_andb' ?x) => unify x Original_LF__DOT__Basics_LF_Basics_andb'_iso; constructor : typeclass_instances.


End Interface.