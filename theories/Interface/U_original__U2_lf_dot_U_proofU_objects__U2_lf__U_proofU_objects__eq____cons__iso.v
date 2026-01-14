From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__eq__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__eq__iso.

  Export Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__eq__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso.Interface <+ Interface.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__eq__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_eq__cons : forall (x : Type) (x0 x1 : x) (x2 x3 : imported_Original_LF__DOT__Poly_LF_Poly_list x),
  imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_eq x0 x1 ->
  imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_eq x2 x3 ->
  imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_eq (imported_Original_LF__DOT__Poly_LF_Poly_cons x0 x2) (imported_Original_LF__DOT__Poly_LF_Poly_cons x1 x3).
Parameter Original_LF__DOT__ProofObjects_LF_ProofObjects_eq__cons_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (hx0 : rel_iso hx x3 x4) (x5 : x1) (x6 : x2) (hx1 : rel_iso hx x5 x6) (x7 : Original.LF_DOT_Poly.LF.Poly.list x1)
    (x8 : imported_Original_LF__DOT__Poly_LF_Poly_list x2) (hx2 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x7 x8) (x9 : Original.LF_DOT_Poly.LF.Poly.list x1)
    (x10 : imported_Original_LF__DOT__Poly_LF_Poly_list x2) (hx3 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x9 x10) (x11 : Original.LF_DOT_ProofObjects.LF.ProofObjects.eq x3 x5)
    (x12 : imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_eq x4 x6),
  rel_iso (Original_LF__DOT__ProofObjects_LF_ProofObjects_eq_iso hx0 hx1) x11 x12 ->
  forall (x13 : Original.LF_DOT_ProofObjects.LF.ProofObjects.eq x7 x9) (x14 : imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_eq x8 x10),
  rel_iso (Original_LF__DOT__ProofObjects_LF_ProofObjects_eq_iso hx2 hx3) x13 x14 ->
  rel_iso (Original_LF__DOT__ProofObjects_LF_ProofObjects_eq_iso (Original_LF__DOT__Poly_LF_Poly_cons_iso hx0 hx2) (Original_LF__DOT__Poly_LF_Poly_cons_iso hx1 hx3))
    (Original.LF_DOT_ProofObjects.LF.ProofObjects.eq_cons x1 x3 x5 x7 x9 x11 x13) (imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_eq__cons x12 x14).
Existing Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_eq__cons_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.eq_cons ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_eq__cons_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.eq_cons imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_eq__cons ?x) => unify x Original_LF__DOT__ProofObjects_LF_ProofObjects_eq__cons_iso; constructor : typeclass_instances.


End Interface.