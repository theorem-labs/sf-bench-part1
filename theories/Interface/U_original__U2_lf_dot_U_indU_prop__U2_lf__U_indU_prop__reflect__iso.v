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

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_reflect : SProp -> imported_Original_LF__DOT__Basics_LF_Basics_bool -> SProp.
Parameter Original_LF__DOT__IndProp_LF_IndProp_reflect_iso : forall (x1 : Prop) (x2 : SProp),
  Iso x1 x2 ->
  forall (x3 : Original.LF_DOT_Basics.LF.Basics.bool) (x4 : imported_Original_LF__DOT__Basics_LF_Basics_bool),
  rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso x3 x4 -> Iso (Original.LF_DOT_IndProp.LF.IndProp.reflect x1 x3) (imported_Original_LF__DOT__IndProp_LF_IndProp_reflect x2 x4).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_reflect_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.reflect ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_reflect_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.reflect imported_Original_LF__DOT__IndProp_LF_IndProp_reflect ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_reflect_iso; constructor : typeclass_instances.


End Interface.