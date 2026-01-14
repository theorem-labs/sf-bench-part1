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

Parameter imported_Original_LF__DOT__Poly_LF_Poly_prod : Type -> Type -> Type.
Parameter Original_LF__DOT__Poly_LF_Poly_prod_iso : forall x1 x2 : Type, Iso x1 x2 -> forall x3 x4 : Type, Iso x3 x4 -> Iso (Original.LF_DOT_Poly.LF.Poly.prod x1 x3) (imported_Original_LF__DOT__Poly_LF_Poly_prod x2 x4).
Existing Instance Original_LF__DOT__Poly_LF_Poly_prod_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.prod ?x) => unify x Original_LF__DOT__Poly_LF_Poly_prod_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.prod imported_Original_LF__DOT__Poly_LF_Poly_prod ?x) => unify x Original_LF__DOT__Poly_LF_Poly_prod_iso; constructor : typeclass_instances.


End Interface.