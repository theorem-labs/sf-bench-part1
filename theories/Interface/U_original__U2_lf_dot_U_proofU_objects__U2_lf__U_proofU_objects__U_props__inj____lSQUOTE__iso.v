From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__U_props__or__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__U_props__or__iso.

  Export Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__U_props__or__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__U_props__or__iso.Args <+ Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__U_props__or__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_inj__l' : forall x x0 : SProp, x -> imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or x x0.
Parameter Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_inj__l'_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : Prop) (x4 : SProp) (hx0 : Iso x3 x4) (x5 : x1) (x6 : x2),
  rel_iso hx x5 x6 ->
  rel_iso (Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or_iso hx hx0) (Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.inj_l' x1 x3 x5)
    (imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_inj__l' x4 x6).
Existing Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_inj__l'_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.inj_l' ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_inj__l'_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.inj_l' imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_inj__l' ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_inj__l'_iso; constructor : typeclass_instances.


End Interface.