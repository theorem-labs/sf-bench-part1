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

Parameter imported_Nat_pred : imported_nat -> imported_nat.
Parameter Nat_pred_iso : forall (x1 : nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> rel_iso nat_iso (Nat.pred x1) (imported_Nat_pred x2).
Existing Instance Nat_pred_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Nat.pred ?x) => unify x Nat_pred_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Nat.pred imported_Nat_pred ?x) => unify x Nat_pred_iso; constructor : typeclass_instances.


End Interface.