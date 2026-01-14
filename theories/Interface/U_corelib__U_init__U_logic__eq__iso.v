From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_true__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_true__iso.

  Export Interface.U_true__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_true__iso.Args <+ Interface.U_true__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Corelib_Init_Logic_eq : forall x : Type, x -> x -> SProp.
Parameter Corelib_Init_Logic_eq_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq x4 x6).
Existing Instance Corelib_Init_Logic_eq_iso.
#[export] Hint Extern 0 (IsoStatementProofFor (@Corelib.Init.Logic.eq) ?x) => unify x Corelib_Init_Logic_eq_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween (@Corelib.Init.Logic.eq) imported_Corelib_Init_Logic_eq ?x) => unify x Corelib_Init_Logic_eq_iso; constructor : typeclass_instances.
Parameter imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp.
Parameter Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2), rel_iso hx x3 x4 -> forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Existing Instance Corelib_Init_Logic_eq_iso_Prop.
#[export] Hint Extern 0 (IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) ?x) => unify x Corelib_Init_Logic_eq_iso_Prop; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween (@Corelib.Init.Logic.eq) imported_Corelib_Init_Logic_eq_Prop ?x) => unify x Corelib_Init_Logic_eq_iso_Prop; constructor : typeclass_instances.


End Interface.