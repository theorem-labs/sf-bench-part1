From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__U_props__U_false__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__U_props__U_false__iso.

  Export Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__U_props__U_false__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__U_props__U_false__iso.Args <+ Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__U_props__U_false__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex__falso__quodlibet' : forall x : Type, imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_False -> x.
Parameter Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex__falso__quodlibet'_iso : forall (x1 x2 : Type) (hx : IsoOrSortRelaxed x1 x2) (x3 : Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.False) (x4 : imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_False),
  rel_iso Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_False_iso x3 x4 ->
  rel_iso_sort hx (Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.ex_falso_quodlibet' x1 x3) (imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex__falso__quodlibet' x2 x4).
Existing Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex__falso__quodlibet'_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.ex_falso_quodlibet' ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex__falso__quodlibet'_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.ex_falso_quodlibet' imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex__falso__quodlibet' ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex__falso__quodlibet'_iso; constructor : typeclass_instances.


End Interface.