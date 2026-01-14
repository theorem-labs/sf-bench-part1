From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__proof____irrelevance__iso Interface.iff__iso Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__propositional____extensionality__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__proof____irrelevance__iso Interface.iff__iso Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__propositional____extensionality__iso.

  Export Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__proof____irrelevance__iso.CodeBlocks Interface.iff__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__propositional____extensionality__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__proof____irrelevance__iso.Interface <+ Interface.iff__iso.Interface <+ Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__propositional____extensionality__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_pe__implies__pi : (forall x x0 : SProp, imported_iff x x0 -> imported_Corelib_Init_Logic_eq x x0) -> forall (x0 : SProp) (x1 x2 : x0), imported_Corelib_Init_Logic_eq_Prop x1 x2.
Parameter Original_LF__DOT__ProofObjects_LF_ProofObjects_pe__implies__pi_iso : forall (x1 : Original.LF_DOT_ProofObjects.LF.ProofObjects.propositional_extensionality) (x2 : forall x x0 : SProp, imported_iff x x0 -> @imported_Corelib_Init_Logic_eq SProp x x0),
  (forall (x3 : Prop) (x4 : SProp) (hx : Iso x3 x4) (x5 : Prop) (x6 : SProp) (hx0 : Iso x5 x6) (x7 : x3 <-> x5) (x8 : imported_iff x4 x6),
   @rel_iso (x3 <-> x5) (imported_iff x4 x6) (@relax_Iso_Ts_Ps (x3 <-> x5) (imported_iff x4 x6) (@iff_iso x3 x4 hx x5 x6 hx0)) x7 x8 ->
   @rel_iso (x3 = x5) (@imported_Corelib_Init_Logic_eq SProp x4 x6)
     (@relax_Iso_Ts_Ps (x3 = x5) (@imported_Corelib_Init_Logic_eq SProp x4 x6)
        (@Corelib_Init_Logic_eq_iso Prop SProp iso_Prop_SProp x3 x4 (@rel_iso_iso_sort_of_iso_Ts_Ps_pe x1 x3 x4 hx) x5 x6 (@rel_iso_iso_sort_of_iso_Ts_Ps_pe x1 x5 x6 hx0)))
     (x1 x3 x5 x7) (x2 x4 x6 x8)) ->
  forall (x3 : Prop) (x4 : SProp) (hx0 : Iso x3 x4) (x5 : x3) (x6 : x4) (hx1 : @rel_iso x3 x4 hx0 x5 x6) (x7 : x3) (x8 : x4) (hx2 : @rel_iso x3 x4 hx0 x7 x8),
  @rel_iso (x5 = x7) (@imported_Corelib_Init_Logic_eq_Prop x4 x6 x8) (@Corelib_Init_Logic_eq_iso_Prop x3 x4 hx0 x5 x6 hx1 x7 x8 hx2)
    (Original.LF_DOT_ProofObjects.LF.ProofObjects.pe_implies_pi x1 x3 x5 x7) (@imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_pe__implies__pi x2 x4 x6 x8).
Existing Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_pe__implies__pi_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.pe_implies_pi ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_pe__implies__pi_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.pe_implies_pi imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_pe__implies__pi ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_pe__implies__pi_iso; constructor : typeclass_instances.


End Interface.