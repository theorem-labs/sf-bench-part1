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

Parameter imported_Original_LF_Rel_next__nat : imported_nat -> imported_nat -> SProp.
Parameter Original_LF_Rel_next__nat_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 -> forall (x3 : nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> Iso (Original.LF.Rel.next_nat x1 x3) (imported_Original_LF_Rel_next__nat x2 x4).
Existing Instance Original_LF_Rel_next__nat_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF.Rel.next_nat ?x) => unify x Original_LF_Rel_next__nat_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF.Rel.next_nat imported_Original_LF_Rel_next__nat ?x) => unify x Original_LF_Rel_next__nat_iso; constructor : typeclass_instances.


End Interface.