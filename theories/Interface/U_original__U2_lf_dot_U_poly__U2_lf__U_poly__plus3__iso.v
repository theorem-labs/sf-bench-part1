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

Parameter imported_Original_LF__DOT__Poly_LF_Poly_plus3 : imported_nat -> imported_nat.
Parameter Original_LF__DOT__Poly_LF_Poly_plus3_iso : forall (x1 : nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> rel_iso nat_iso (Original.LF_DOT_Poly.LF.Poly.plus3 x1) (imported_Original_LF__DOT__Poly_LF_Poly_plus3 x2).
Existing Instance Original_LF__DOT__Poly_LF_Poly_plus3_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.plus3 ?x) => unify x Original_LF__DOT__Poly_LF_Poly_plus3_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.plus3 imported_Original_LF__DOT__Poly_LF_Poly_plus3 ?x) => unify x Original_LF__DOT__Poly_LF_Poly_plus3_iso; constructor : typeclass_instances.


End Interface.