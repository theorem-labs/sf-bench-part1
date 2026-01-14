From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf__U_rel__relation__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.U_original__U2_lf__U_rel__antisymmetric__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__le__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf__U_rel__relation__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.U_original__U2_lf__U_rel__antisymmetric__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__le__iso.

  Export Interface.U_original__U2_lf__U_rel__relation__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.U_original__U2_lf__U_rel__antisymmetric__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__le__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf__U_rel__relation__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.U_original__U2_lf__U_rel__antisymmetric__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__le__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF_Rel_le__antisymmetric : forall x x0 : imported_nat, imported_Original_LF__DOT__IndProp_LF_IndProp_le x x0 -> imported_Original_LF__DOT__IndProp_LF_IndProp_le x0 x -> imported_Corelib_Init_Logic_eq x x0.
Parameter Original_LF_Rel_le__antisymmetric_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) (x5 : Original.LF_DOT_IndProp.LF.IndProp.le x1 x3)
    (x6 : imported_Original_LF__DOT__IndProp_LF_IndProp_le x2 x4),
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_le_iso hx hx0) x5 x6 ->
  forall (x7 : Original.LF_DOT_IndProp.LF.IndProp.le x3 x1) (x8 : imported_Original_LF__DOT__IndProp_LF_IndProp_le x4 x2),
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_le_iso hx0 hx) x7 x8 ->
  rel_iso (Corelib_Init_Logic_eq_iso hx hx0) (Original.LF.Rel.le_antisymmetric x1 x3 x5 x7) (imported_Original_LF_Rel_le__antisymmetric x6 x8).
Existing Instance Original_LF_Rel_le__antisymmetric_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF.Rel.le_antisymmetric ?x) => unify x Original_LF_Rel_le__antisymmetric_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF.Rel.le_antisymmetric imported_Original_LF_Rel_le__antisymmetric ?x) => unify x Original_LF_Rel_le__antisymmetric_iso; constructor : typeclass_instances.


End Interface.