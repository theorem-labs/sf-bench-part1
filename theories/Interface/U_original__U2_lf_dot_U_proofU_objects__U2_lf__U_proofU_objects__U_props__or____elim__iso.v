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

Parameter imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or__elim : forall x x0 x1 : SProp, imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or x x0 -> (x -> x1) -> (x0 -> x1) -> x1.
Parameter Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or__elim_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : Prop) (x4 : SProp) (hx0 : Iso x3 x4) (x5 : Prop) (x6 : SProp) (hx1 : Iso x5 x6)
    (x7 : Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.or x1 x3) (x8 : imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or x2 x4),
  rel_iso (Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or_iso hx hx0) x7 x8 ->
  forall (x9 : x1 -> x5) (x10 : x2 -> x6),
  (forall (x11 : x1) (x12 : x2), rel_iso hx x11 x12 -> rel_iso hx1 (x9 x11) (x10 x12)) ->
  forall (x11 : x3 -> x5) (x12 : x4 -> x6),
  (forall (x13 : x3) (x14 : x4), rel_iso hx0 x13 x14 -> rel_iso hx1 (x11 x13) (x12 x14)) ->
  rel_iso hx1 (Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.or_elim x1 x3 x5 x7 x9 x11) (imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or__elim x8 x10 x12).
Existing Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or__elim_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.or_elim ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or__elim_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.or_elim imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or__elim ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or__elim_iso; constructor : typeclass_instances.


End Interface.