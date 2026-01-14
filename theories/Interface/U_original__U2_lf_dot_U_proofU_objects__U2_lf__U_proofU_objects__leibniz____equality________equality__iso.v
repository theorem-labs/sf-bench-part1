From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__eq__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__eq__iso.

  Export Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__eq__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__eq__iso.Args <+ Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__eq__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_leibniz__equality____equality : forall (x : Type) (x0 x1 : x), (forall x2 : x -> SProp, x2 x0 -> x2 x1) -> imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_eq x0 x1.
Parameter Original_LF__DOT__ProofObjects_LF_ProofObjects_leibniz__equality____equality_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (hx0 : rel_iso hx x3 x4) (x5 : x1) (x6 : x2) (hx1 : rel_iso hx x5 x6) (x7 : forall P : x1 -> Prop, P x3 -> P x5)
    (x8 : forall x : x2 -> SProp, x x4 -> x x6),
  (forall (x9 : x1 -> Prop) (x10 : x2 -> SProp) (hx2 : forall (x11 : x1) (x12 : x2), rel_iso hx x11 x12 -> Iso (x9 x11) (x10 x12)) (x11 : x9 x3) (x12 : x10 x4),
   rel_iso (hx2 x3 x4 hx0) x11 x12 -> rel_iso (hx2 x5 x6 hx1) (x7 x9 x11) (x8 x10 x12)) ->
  rel_iso (Original_LF__DOT__ProofObjects_LF_ProofObjects_eq_iso hx0 hx1) (Original.LF_DOT_ProofObjects.LF.ProofObjects.leibniz_equality__equality x1 x3 x5 x7)
    (imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_leibniz__equality____equality x8).
Existing Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_leibniz__equality____equality_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.leibniz_equality__equality ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_leibniz__equality____equality_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.leibniz_equality__equality imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_leibniz__equality____equality ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_leibniz__equality____equality_iso; constructor : typeclass_instances.


End Interface.