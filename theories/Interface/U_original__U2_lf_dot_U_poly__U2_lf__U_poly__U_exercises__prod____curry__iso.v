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

Parameter imported_Original_LF__DOT__Poly_LF_Poly_Exercises_prod__curry : forall x x0 x1 : Type, (imported_Original_LF__DOT__Poly_LF_Poly_prod x x0 -> x1) -> x -> x0 -> x1.
Parameter Original_LF__DOT__Poly_LF_Poly_Exercises_prod__curry_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 x4 : Type) (hx0 : Iso x3 x4) (x5 x6 : Type) (hx1 : IsoOrSortRelaxed x5 x6) (x7 : Original.LF_DOT_Poly.LF.Poly.prod x1 x3 -> x5)
    (x8 : imported_Original_LF__DOT__Poly_LF_Poly_prod x2 x4 -> x6),
  (forall (x9 : Original.LF_DOT_Poly.LF.Poly.prod x1 x3) (x10 : imported_Original_LF__DOT__Poly_LF_Poly_prod x2 x4),
   rel_iso (Original_LF__DOT__Poly_LF_Poly_prod_iso hx hx0) x9 x10 -> rel_iso_sort hx1 (x7 x9) (x8 x10)) ->
  forall (x9 : x1) (x10 : x2),
  rel_iso hx x9 x10 ->
  forall (x11 : x3) (x12 : x4),
  rel_iso hx0 x11 x12 -> rel_iso_sort hx1 (Original.LF_DOT_Poly.LF.Poly.Exercises.prod_curry x7 x9 x11) (imported_Original_LF__DOT__Poly_LF_Poly_Exercises_prod__curry x8 x10 x12).
Existing Instance Original_LF__DOT__Poly_LF_Poly_Exercises_prod__curry_iso.
#[export] Hint Extern 0 (IsoStatementProofFor (@Original.LF_DOT_Poly.LF.Poly.Exercises.prod_curry) ?x) => unify x Original_LF__DOT__Poly_LF_Poly_Exercises_prod__curry_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween (@Original.LF_DOT_Poly.LF.Poly.Exercises.prod_curry) imported_Original_LF__DOT__Poly_LF_Poly_Exercises_prod__curry ?x) => unify x Original_LF__DOT__Poly_LF_Poly_Exercises_prod__curry_iso; constructor : typeclass_instances.


End Interface.