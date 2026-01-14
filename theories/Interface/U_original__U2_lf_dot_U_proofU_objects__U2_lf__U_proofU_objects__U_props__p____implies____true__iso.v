From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__U_props__U_true__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__U_props__U_true__iso.

  Export Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__U_props__U_true__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__U_props__U_true__iso.Args <+ Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__U_props__U_true__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_p__implies__true : forall x : Type, x -> imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_True.
Parameter Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_p__implies__true_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2),
  rel_iso hx x3 x4 ->
  rel_iso Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_True_iso (Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.p_implies_true x1 x3)
    (imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_p__implies__true x4).
Existing Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_p__implies__true_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.p_implies_true ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_p__implies__true_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.p_implies_true imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_p__implies__true ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_p__implies__true_iso; constructor : typeclass_instances.


End Interface.