From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__cnat__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__cnat__iso.

  Export Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__cnat__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__cnat__iso.Args <+ Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__U_exercises__cnat__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Poly_LF_Poly_Exercises_scc : (forall x : Type, (x -> x) -> x -> x) -> forall x0 : Type, (x0 -> x0) -> x0 -> x0.
Parameter Original_LF__DOT__Poly_LF_Poly_Exercises_scc_iso : forall (x1 : Original.LF_DOT_Poly.LF.Poly.Exercises.cnat) (x2 : forall x : Type, (x -> x) -> x -> x),
  (forall (x3 x4 : Type) (hx : Iso x3 x4) (x5 : x3 -> x3) (x6 : x4 -> x4),
   (forall (x7 : x3) (x8 : x4), rel_iso hx x7 x8 -> rel_iso hx (x5 x7) (x6 x8)) -> forall (x7 : x3) (x8 : x4), rel_iso hx x7 x8 -> rel_iso hx (x1 x3 x5 x7) (x2 x4 x6 x8)) ->
  forall (x3 x4 : Type) (hx0 : Iso x3 x4) (x5 : x3 -> x3) (x6 : x4 -> x4),
  (forall (x7 : x3) (x8 : x4), rel_iso hx0 x7 x8 -> rel_iso hx0 (x5 x7) (x6 x8)) ->
  forall (x7 : x3) (x8 : x4), rel_iso hx0 x7 x8 -> rel_iso hx0 (Original.LF_DOT_Poly.LF.Poly.Exercises.scc x1 x3 x5 x7) (imported_Original_LF__DOT__Poly_LF_Poly_Exercises_scc x2 x6 x8).
Existing Instance Original_LF__DOT__Poly_LF_Poly_Exercises_scc_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.Exercises.scc ?x) => unify x Original_LF__DOT__Poly_LF_Poly_Exercises_scc_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.Exercises.scc imported_Original_LF__DOT__Poly_LF_Poly_Exercises_scc ?x) => unify x Original_LF__DOT__Poly_LF_Poly_Exercises_scc_iso; constructor : typeclass_instances.


End Interface.