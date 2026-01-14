From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.bool__iso Interface.nat__iso.

Module Export CodeBlocks.

  Export (hints) Interface.bool__iso Interface.nat__iso.

  Export Interface.bool__iso.CodeBlocks Interface.nat__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.bool__iso.Interface <+ Interface.nat__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_PeanoNat_Nat_leb : imported_nat -> imported_nat -> imported_bool.
Parameter PeanoNat_Nat_leb_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 -> forall (x3 : nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> rel_iso bool_iso (PeanoNat.Nat.leb x1 x3) (imported_PeanoNat_Nat_leb x2 x4).
Existing Instance PeanoNat_Nat_leb_iso.
#[export] Hint Extern 0 (IsoStatementProofFor PeanoNat.Nat.leb ?x) => unify x PeanoNat_Nat_leb_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween PeanoNat.Nat.leb imported_PeanoNat_Nat_leb ?x) => unify x PeanoNat_Nat_leb_iso; constructor : typeclass_instances.


End Interface.