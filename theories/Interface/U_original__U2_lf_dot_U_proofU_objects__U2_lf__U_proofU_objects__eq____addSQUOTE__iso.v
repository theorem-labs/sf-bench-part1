From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__eq__iso Interface.nat__iso Interface.U_s__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__eq__iso Interface.nat__iso Interface.U_s__iso.

  Export Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_s__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_s__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_eq__add' : forall x x0 : imported_nat, imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_eq x x0 -> imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_eq (imported_S x) (imported_S x0).
Parameter Original_LF__DOT__ProofObjects_LF_ProofObjects_eq__add'_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) (x5 : Original.LF_DOT_ProofObjects.LF.ProofObjects.eq x1 x3)
    (x6 : imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_eq x2 x4),
  rel_iso (Original_LF__DOT__ProofObjects_LF_ProofObjects_eq_iso hx hx0) x5 x6 ->
  rel_iso (Original_LF__DOT__ProofObjects_LF_ProofObjects_eq_iso (S_iso hx) (S_iso hx0)) (Original.LF_DOT_ProofObjects.LF.ProofObjects.eq_add' x1 x3 x5)
    (imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_eq__add' x6).
Existing Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_eq__add'_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.eq_add' ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_eq__add'_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.eq_add' imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_eq__add' ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_eq__add'_iso; constructor : typeclass_instances.


End Interface.