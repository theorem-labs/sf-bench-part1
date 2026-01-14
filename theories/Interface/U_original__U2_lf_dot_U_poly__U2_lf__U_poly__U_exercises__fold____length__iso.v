From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.nat__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso Interface.nat__iso.

  Export Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.CodeBlocks Interface.nat__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.Interface <+ Interface.nat__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length : forall x : Type, imported_Original_LF__DOT__Poly_LF_Poly_list x -> imported_nat.
Parameter Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_Poly.LF.Poly.list x1) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x3 x4 ->
  rel_iso nat_iso (Original.LF_DOT_Poly.LF.Poly.Exercises.fold_length x3) (imported_Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length x4).
Existing Instance Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length_iso.
#[export] Hint Extern 0 (IsoStatementProofFor (@Original.LF_DOT_Poly.LF.Poly.Exercises.fold_length) ?x) => unify x Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween (@Original.LF_DOT_Poly.LF.Poly.Exercises.fold_length) imported_Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length ?x) => unify x Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length_iso; constructor : typeclass_instances.


End Interface.