From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.nat__iso.

Module Export CodeBlocks.

  Export (hints) Interface.nat__iso.

  Export Interface.nat__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.nat__iso.Args <+ Interface.nat__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Poly_LF_Poly_constfun : forall x : Type, x -> imported_nat -> x.
Parameter Original_LF__DOT__Poly_LF_Poly_constfun_iso : forall (x1 x2 : Type) (hx : IsoOrSortRelaxed x1 x2) (x3 : x1) (x4 : x2),
  rel_iso_sort hx x3 x4 ->
  forall (x5 : nat) (x6 : imported_nat), rel_iso nat_iso x5 x6 -> rel_iso_sort hx (Original.LF_DOT_Poly.LF.Poly.constfun x3 x5) (imported_Original_LF__DOT__Poly_LF_Poly_constfun x4 x6).
Existing Instance Original_LF__DOT__Poly_LF_Poly_constfun_iso.
#[export] Hint Extern 0 (IsoStatementProofFor (@Original.LF_DOT_Poly.LF.Poly.constfun) ?x) => unify x Original_LF__DOT__Poly_LF_Poly_constfun_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween (@Original.LF_DOT_Poly.LF.Poly.constfun) imported_Original_LF__DOT__Poly_LF_Poly_constfun ?x) => unify x Original_LF__DOT__Poly_LF_Poly_constfun_iso; constructor : typeclass_instances.


End Interface.