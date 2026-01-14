From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.U_type__iso Interface.iff__iso Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__propositional____extensionality__iso Interface.or__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.U_type__iso Interface.iff__iso Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__propositional____extensionality__iso Interface.or__iso.

  Export Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.U_type__iso.CodeBlocks Interface.iff__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__propositional____extensionality__iso.CodeBlocks Interface.or__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.U_type__iso.Interface <+ Interface.iff__iso.Interface <+ Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__propositional____extensionality__iso.Interface <+ Interface.or__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_pe__implies__or__eq : (forall x x0 : SProp, imported_iff x x0 -> imported_Corelib_Init_Logic_eq x x0) -> forall x0 x1 : SProp, imported_Corelib_Init_Logic_eq (imported_or x0 x1) (imported_or x1 x0).
Parameter Original_LF__DOT__ProofObjects_LF_ProofObjects_pe__implies__or__eq_iso : forall (x1 : Original.LF_DOT_ProofObjects.LF.ProofObjects.propositional_extensionality) (x2 : forall x x0 : SProp, imported_iff x x0 -> @imported_Corelib_Init_Logic_eq SProp x x0),
  (forall (x3 : Prop) (x4 : SProp) (hx : Iso x3 x4) (x5 : Prop) (x6 : SProp) (hx0 : Iso x5 x6) (x7 : x3 <-> x5) (x8 : imported_iff x4 x6),
   @rel_iso (x3 <-> x5) (imported_iff x4 x6) (@relax_Iso_Ts_Ps (x3 <-> x5) (imported_iff x4 x6) (@iff_iso x3 x4 hx x5 x6 hx0)) x7 x8 ->
   @rel_iso (x3 = x5) (@imported_Corelib_Init_Logic_eq SProp x4 x6)
     (@relax_Iso_Ts_Ps (x3 = x5) (@imported_Corelib_Init_Logic_eq SProp x4 x6)
        (@Corelib_Init_Logic_eq_iso Prop SProp iso_Prop_SProp x3 x4 (@rel_iso_iso_sort_of_iso_Ts_Ps_pe x1 x3 x4 hx) x5 x6 (@rel_iso_iso_sort_of_iso_Ts_Ps_pe x1 x5 x6 hx0)))
     (x1 x3 x5 x7) (x2 x4 x6 x8)) ->
  forall (x3 : Prop) (x4 : SProp) (hx0 : Iso x3 x4) (x5 : Prop) (x6 : SProp) (hx1 : Iso x5 x6),
  @rel_iso ((x3 \/ x5) = (x5 \/ x3)) (@imported_Corelib_Init_Logic_eq SProp (imported_or x4 x6) (imported_or x6 x4))
    (@relax_Iso_Ts_Ps ((x3 \/ x5) = (x5 \/ x3)) (@imported_Corelib_Init_Logic_eq SProp (imported_or x4 x6) (imported_or x6 x4))
       (@Corelib_Init_Logic_eq_iso Prop SProp iso_Prop_SProp (x3 \/ x5) (imported_or x4 x6) (@rel_iso_iso_sort_of_iso_Ts_Ps_pe x1 (x3 \/ x5) (imported_or x4 x6) (@or_iso x3 x4 hx0 x5 x6 hx1))
          (x5 \/ x3) (imported_or x6 x4) (@rel_iso_iso_sort_of_iso_Ts_Ps_pe x1 (x5 \/ x3) (imported_or x6 x4) (@or_iso x5 x6 hx1 x3 x4 hx0))))
    (Original.LF_DOT_ProofObjects.LF.ProofObjects.pe_implies_or_eq x1 x3 x5) (imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_pe__implies__or__eq x2 x4 x6).
Existing Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_pe__implies__or__eq_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.pe_implies_or_eq ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_pe__implies__or__eq_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.pe_implies_or_eq imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_pe__implies__or__eq ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_pe__implies__or__eq_iso; constructor : typeclass_instances.


End Interface.