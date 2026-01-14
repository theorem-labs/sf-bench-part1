From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

Module Export CodeBlocks.

#[export] Instance: MustUnfold Original.LF_DOT_Poly.LF.Poly.Exercises.cnat := {}.

End CodeBlocks.

Module Type Args. End Args.

Module Type Interface (Import args : Args).

Definition imported_Original_LF__DOT__Poly_LF_Poly_Exercises_cnat : Type
  := forall x2 : Type, (x2 -> x2) -> x2 -> x2.
Definition Original_LF__DOT__Poly_LF_Poly_Exercises_cnat_iso : forall x1 x2 : Type, Iso x1 x2 -> Iso ((x1 -> x1) -> x1 -> x1) ((x2 -> x2) -> x2 -> x2)
  := fun (x1 x2 : Type) (hx : Iso x1 x2) => IsoArrow (IsoArrow hx hx) (IsoArrow hx hx).
Existing Instance Original_LF__DOT__Poly_LF_Poly_Exercises_cnat_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.Exercises.cnat ?x) => unify x Original_LF__DOT__Poly_LF_Poly_Exercises_cnat_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.Exercises.cnat imported_Original_LF__DOT__Poly_LF_Poly_Exercises_cnat ?x) => unify x Original_LF__DOT__Poly_LF_Poly_Exercises_cnat_iso; constructor : typeclass_instances.


End Interface.