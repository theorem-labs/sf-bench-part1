From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf__U_rel__relation__iso Interface.U_original__U2_lf__U_rel__reflexive__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__le__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf__U_rel__relation__iso Interface.U_original__U2_lf__U_rel__reflexive__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__le__iso.

  Export Interface.U_original__U2_lf__U_rel__relation__iso.CodeBlocks Interface.U_original__U2_lf__U_rel__reflexive__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__le__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf__U_rel__relation__iso.Interface <+ Interface.U_original__U2_lf__U_rel__reflexive__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__le__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF_Rel_le__reflexive : forall x : imported_nat, imported_Original_LF__DOT__IndProp_LF_IndProp_le x x.
Parameter Original_LF_Rel_le__reflexive_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2),
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_le_iso hx hx) (Original.LF.Rel.le_reflexive x1) (imported_Original_LF_Rel_le__reflexive x2).
Existing Instance Original_LF_Rel_le__reflexive_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF.Rel.le_reflexive ?x) => unify x Original_LF_Rel_le__reflexive_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF.Rel.le_reflexive imported_Original_LF_Rel_le__reflexive ?x) => unify x Original_LF_Rel_le__reflexive_iso; constructor : typeclass_instances.


End Interface.