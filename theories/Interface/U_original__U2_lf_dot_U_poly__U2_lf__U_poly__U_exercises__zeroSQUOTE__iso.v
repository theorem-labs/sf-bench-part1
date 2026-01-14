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

Parameter imported_Original_LF__DOT__Poly_LF_Poly_Exercises_zero' : forall x : Type, (x -> x) -> x -> x.
Parameter Original_LF__DOT__Poly_LF_Poly_Exercises_zero'_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1 -> x1) (x4 : x2 -> x2),
  (forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> rel_iso hx (x3 x5) (x4 x6)) ->
  forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> rel_iso hx (Original.LF_DOT_Poly.LF.Poly.Exercises.zero' x1 x3 x5) (imported_Original_LF__DOT__Poly_LF_Poly_Exercises_zero' x4 x6).
Existing Instance Original_LF__DOT__Poly_LF_Poly_Exercises_zero'_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.Exercises.zero' ?x) => unify x Original_LF__DOT__Poly_LF_Poly_Exercises_zero'_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.Exercises.zero' imported_Original_LF__DOT__Poly_LF_Poly_Exercises_zero' ?x) => unify x Original_LF__DOT__Poly_LF_Poly_Exercises_zero'_iso; constructor : typeclass_instances.


End Interface.