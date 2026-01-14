From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__U_props__U_false__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_s__iso Interface.__0__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__U_props__U_false__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.nat__iso Interface.U_s__iso Interface.__0__iso.

  Export Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__U_props__U_false__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__U_props__U_false__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_false__implies__zero__eq__one : imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_False -> imported_Corelib_Init_Logic_eq imported_0 (imported_S imported_0).
Parameter Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_false__implies__zero__eq__one_iso : forall (x1 : Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.False) (x2 : imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_False),
  rel_iso Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_False_iso x1 x2 ->
  rel_iso (Corelib_Init_Logic_eq_iso _0_iso (S_iso _0_iso)) (Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.false_implies_zero_eq_one x1)
    (imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_false__implies__zero__eq__one x2).
Existing Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_false__implies__zero__eq__one_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.false_implies_zero_eq_one ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_false__implies__zero__eq__one_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.false_implies_zero_eq_one imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_false__implies__zero__eq__one ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_false__implies__zero__eq__one_iso; constructor : typeclass_instances.


End Interface.