From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__U_props__ex__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__ev__iso Interface.U_s__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__U_props__ex__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__ev__iso Interface.U_s__iso.

  Export Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__U_props__ex__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__ev__iso.CodeBlocks Interface.U_s__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__U_props__ex__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__ev__iso.Interface <+ Interface.U_s__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex__ev__Sn : imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex (fun H : imported_nat => imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev (imported_S H)).
Parameter Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex__ev__Sn_iso : rel_iso
    (relax_Iso_Ts_Ps
       (Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex_iso (fun n : nat => Original.LF_DOT_ProofObjects.LF.ProofObjects.ev (S n))
          (fun H : imported_nat => imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev (imported_S H))
          (fun (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) => Original_LF__DOT__ProofObjects_LF_ProofObjects_ev_iso (S_iso hx))))
    Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.ex_ev_Sn imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex__ev__Sn.
Existing Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex__ev__Sn_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.ex_ev_Sn ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex__ev__Sn_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.ex_ev_Sn imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex__ev__Sn ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex__ev__Sn_iso; constructor : typeclass_instances.


End Interface.