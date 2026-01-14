From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.

  Export Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Args <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Poly_LF_Poly_fold : forall x x0 : Type, (x -> x0 -> x0) -> imported_Original_LF__DOT__Poly_LF_Poly_list x -> x0 -> x0.
Parameter Original_LF__DOT__Poly_LF_Poly_fold_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 x4 : Type) (hx0 : IsoOrSortRelaxed x3 x4) (x5 : x1 -> x3 -> x3) (x6 : x2 -> x4 -> x4),
  (forall (x7 : x1) (x8 : x2), rel_iso hx x7 x8 -> forall (x9 : x3) (x10 : x4), rel_iso_sort hx0 x9 x10 -> rel_iso_sort hx0 (x5 x7 x9) (x6 x8 x10)) ->
  forall (x7 : Original.LF_DOT_Poly.LF.Poly.list x1) (x8 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x7 x8 ->
  forall (x9 : x3) (x10 : x4), rel_iso_sort hx0 x9 x10 -> rel_iso_sort hx0 (Original.LF_DOT_Poly.LF.Poly.fold x5 x7 x9) (imported_Original_LF__DOT__Poly_LF_Poly_fold x6 x8 x10).
Existing Instance Original_LF__DOT__Poly_LF_Poly_fold_iso.
#[export] Hint Extern 0 (IsoStatementProofFor (@Original.LF_DOT_Poly.LF.Poly.fold) ?x) => unify x Original_LF__DOT__Poly_LF_Poly_fold_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween (@Original.LF_DOT_Poly.LF.Poly.fold) imported_Original_LF__DOT__Poly_LF_Poly_fold ?x) => unify x Original_LF__DOT__Poly_LF_Poly_fold_iso; constructor : typeclass_instances.


End Interface.