From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_natU_playground__nat__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_natU_playground__nat__iso.

  Export Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_natU_playground__nat__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_natU_playground__nat__iso.Args <+ Interface.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_natU_playground__nat__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Basics_LF_Basics_NatPlayground_pred : imported_Original_LF__DOT__Basics_LF_Basics_NatPlayground_nat -> imported_Original_LF__DOT__Basics_LF_Basics_NatPlayground_nat.
Parameter Original_LF__DOT__Basics_LF_Basics_NatPlayground_pred_iso : forall (x1 : Original.LF_DOT_Basics.LF.Basics.NatPlayground.nat) (x2 : imported_Original_LF__DOT__Basics_LF_Basics_NatPlayground_nat),
  rel_iso Original_LF__DOT__Basics_LF_Basics_NatPlayground_nat_iso x1 x2 ->
  rel_iso Original_LF__DOT__Basics_LF_Basics_NatPlayground_nat_iso (Original.LF_DOT_Basics.LF.Basics.NatPlayground.pred x1) (imported_Original_LF__DOT__Basics_LF_Basics_NatPlayground_pred x2).
Existing Instance Original_LF__DOT__Basics_LF_Basics_NatPlayground_pred_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.NatPlayground.pred ?x) => unify x Original_LF__DOT__Basics_LF_Basics_NatPlayground_pred_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.NatPlayground.pred imported_Original_LF__DOT__Basics_LF_Basics_NatPlayground_pred ?x) => unify x Original_LF__DOT__Basics_LF_Basics_NatPlayground_pred_iso; constructor : typeclass_instances.


End Interface.