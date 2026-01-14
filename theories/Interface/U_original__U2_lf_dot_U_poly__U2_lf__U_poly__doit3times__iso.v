From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

Module Export CodeBlocks.

End CodeBlocks.

Module Type Args. End Args.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Poly_LF_Poly_doit3times : forall x : Type, (x -> x) -> x -> x.
Parameter Original_LF__DOT__Poly_LF_Poly_doit3times_iso : forall (x1 x2 : Type) (hx : IsoOrSortRelaxed x1 x2) (x3 : x1 -> x1) (x4 : x2 -> x2),
  (forall (x5 : x1) (x6 : x2), rel_iso_sort hx x5 x6 -> rel_iso_sort hx (x3 x5) (x4 x6)) ->
  forall (x5 : x1) (x6 : x2), rel_iso_sort hx x5 x6 -> rel_iso_sort hx (Original.LF_DOT_Poly.LF.Poly.doit3times x3 x5) (imported_Original_LF__DOT__Poly_LF_Poly_doit3times x4 x6).
Existing Instance Original_LF__DOT__Poly_LF_Poly_doit3times_iso.
#[export] Hint Extern 0 (IsoStatementProofFor (@Original.LF_DOT_Poly.LF.Poly.doit3times) ?x) => unify x Original_LF__DOT__Poly_LF_Poly_doit3times_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween (@Original.LF_DOT_Poly.LF.Poly.doit3times) imported_Original_LF__DOT__Poly_LF_Poly_doit3times ?x) => unify x Original_LF__DOT__Poly_LF_Poly_doit3times_iso; constructor : typeclass_instances.


End Interface.