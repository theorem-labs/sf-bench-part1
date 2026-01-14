From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__eq__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__eq__iso.

  Export Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__eq__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso.Interface <+ Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__eq__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_singleton : forall (x : Type) (x0 : x),
  imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_eq
    (imported_Original_LF__DOT__Poly_LF_Poly_app (imported_Original_LF__DOT__Poly_LF_Poly_nil x) (imported_Original_LF__DOT__Poly_LF_Poly_cons x0 (imported_Original_LF__DOT__Poly_LF_Poly_nil x)))
    (imported_Original_LF__DOT__Poly_LF_Poly_cons x0 (imported_Original_LF__DOT__Poly_LF_Poly_nil x)).
Parameter Original_LF__DOT__ProofObjects_LF_ProofObjects_singleton_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (hx0 : rel_iso hx x3 x4),
  rel_iso
    (Original_LF__DOT__ProofObjects_LF_ProofObjects_eq_iso
       (Original_LF__DOT__Poly_LF_Poly_app_iso (Original_LF__DOT__Poly_LF_Poly_nil_iso hx) (Original_LF__DOT__Poly_LF_Poly_cons_iso hx0 (Original_LF__DOT__Poly_LF_Poly_nil_iso hx)))
       (Original_LF__DOT__Poly_LF_Poly_cons_iso hx0 (Original_LF__DOT__Poly_LF_Poly_nil_iso hx)))
    (Original.LF_DOT_ProofObjects.LF.ProofObjects.singleton x1 x3) (imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_singleton x4).
Existing Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_singleton_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.singleton ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_singleton_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.singleton imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_singleton ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_singleton_iso; constructor : typeclass_instances.


End Interface.