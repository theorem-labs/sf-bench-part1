From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__prod__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__prod__iso.

  Export Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__prod__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__prod__iso.Args <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__prod__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Poly_LF_Poly_fst : forall x x0 : Type, imported_Original_LF__DOT__Poly_LF_Poly_prod x x0 -> x.
Parameter Original_LF__DOT__Poly_LF_Poly_fst_iso : forall (x1 x2 : Type) (hx : IsoOrSort x1 x2) (x3 x4 : Type) (hx0 : Iso x3 x4) (x5 : Original.LF_DOT_Poly.LF.Poly.prod x1 x3) (x6 : imported_Original_LF__DOT__Poly_LF_Poly_prod x2 x4),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_prod_iso (Iso_of_IsoOrSortAndRelIso hx) hx0) x5 x6 -> rel_iso_sort hx (Original.LF_DOT_Poly.LF.Poly.fst x5) (imported_Original_LF__DOT__Poly_LF_Poly_fst x6).
Existing Instance Original_LF__DOT__Poly_LF_Poly_fst_iso.
#[export] Hint Extern 0 (IsoStatementProofFor (@Original.LF_DOT_Poly.LF.Poly.fst) ?x) => unify x Original_LF__DOT__Poly_LF_Poly_fst_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween (@Original.LF_DOT_Poly.LF.Poly.fst) imported_Original_LF__DOT__Poly_LF_Poly_fst ?x) => unify x Original_LF__DOT__Poly_LF_Poly_fst_iso; constructor : typeclass_instances.


End Interface.