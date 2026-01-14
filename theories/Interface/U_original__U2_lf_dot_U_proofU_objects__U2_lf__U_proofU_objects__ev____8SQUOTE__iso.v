From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.nat__iso Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__ev__iso Interface.U_s__iso Interface.__0__iso.

Module Export CodeBlocks.

  Export (hints) Interface.nat__iso Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__ev__iso Interface.U_s__iso Interface.__0__iso.

  Export Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__ev__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__ev__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__8' : imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev (imported_S (imported_S (imported_S (iterate1 imported_S 5 imported_0)))).
Parameter Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__8'_iso : rel_iso (Original_LF__DOT__ProofObjects_LF_ProofObjects_ev_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 5 0 imported_0 _0_iso))))) Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_8'
    imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__8'.
Existing Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__8'_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_8' ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__8'_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_8' imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__8' ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__8'_iso; constructor : typeclass_instances.


End Interface.