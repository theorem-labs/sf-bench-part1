From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.bool__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.bool__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.bool__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.bool__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Ascii_Ascii : imported_bool -> imported_bool -> imported_bool -> imported_bool -> imported_bool -> imported_bool -> imported_bool -> imported_bool -> imported_Ascii_ascii.
Parameter Ascii_Ascii_iso : forall (x1 : bool) (x2 : imported_bool),
  rel_iso bool_iso x1 x2 ->
  forall (x3 : bool) (x4 : imported_bool),
  rel_iso bool_iso x3 x4 ->
  forall (x5 : bool) (x6 : imported_bool),
  rel_iso bool_iso x5 x6 ->
  forall (x7 : bool) (x8 : imported_bool),
  rel_iso bool_iso x7 x8 ->
  forall (x9 : bool) (x10 : imported_bool),
  rel_iso bool_iso x9 x10 ->
  forall (x11 : bool) (x12 : imported_bool),
  rel_iso bool_iso x11 x12 ->
  forall (x13 : bool) (x14 : imported_bool),
  rel_iso bool_iso x13 x14 ->
  forall (x15 : bool) (x16 : imported_bool), rel_iso bool_iso x15 x16 -> rel_iso Ascii_ascii_iso (Ascii.Ascii x1 x3 x5 x7 x9 x11 x13 x15) (imported_Ascii_Ascii x2 x4 x6 x8 x10 x12 x14 x16).
Existing Instance Ascii_Ascii_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Ascii.Ascii ?x) => unify x Ascii_Ascii_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Ascii.Ascii imported_Ascii_Ascii ?x) => unify x Ascii_Ascii_iso; constructor : typeclass_instances.


End Interface.