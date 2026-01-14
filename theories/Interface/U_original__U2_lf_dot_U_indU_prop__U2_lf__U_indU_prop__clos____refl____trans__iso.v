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

Parameter imported_Original_LF__DOT__IndProp_LF_IndProp_clos__refl__trans : forall x : Type, (x -> x -> SProp) -> x -> x -> SProp.
Parameter Original_LF__DOT__IndProp_LF_IndProp_clos__refl__trans_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1 -> x1 -> Prop) (x4 : x2 -> x2 -> SProp),
  (forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> forall (x7 : x1) (x8 : x2), rel_iso hx x7 x8 -> Iso (x3 x5 x7) (x4 x6 x8)) ->
  forall (x5 : x1) (x6 : x2),
  rel_iso hx x5 x6 ->
  forall (x7 : x1) (x8 : x2), rel_iso hx x7 x8 -> Iso (Original.LF_DOT_IndProp.LF.IndProp.clos_refl_trans x3 x5 x7) (imported_Original_LF__DOT__IndProp_LF_IndProp_clos__refl__trans x4 x6 x8).
Existing Instance Original_LF__DOT__IndProp_LF_IndProp_clos__refl__trans_iso.
#[export] Hint Extern 0 (IsoStatementProofFor (@Original.LF_DOT_IndProp.LF.IndProp.clos_refl_trans) ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_clos__refl__trans_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween (@Original.LF_DOT_IndProp.LF.IndProp.clos_refl_trans) imported_Original_LF__DOT__IndProp_LF_IndProp_clos__refl__trans ?x) => unify x Original_LF__DOT__IndProp_LF_IndProp_clos__refl__trans_iso; constructor : typeclass_instances.


End Interface.